import SampLib.LatentUniform

/-! # Exposing the physical root of a memoized uniform oracle -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentUniform

/-- The root occurrence in the uniform oracle's prefix-read expression. -/
private def root? {rT : Type} : Exp rT → Option Loc
  | .lam (.cond _ _ (.app _ (.app (.app _ (.lit (.loc l))) _))) => some l
  | _ => none

private theorem root_value {rT : Type} (l : Loc) : root? (value (rT := rT) l).fst = some l := by
  rfl

/-- Two aliases expose the same root precisely when their uniform closures agree. -/
theorem value_injective {rT : Type} : Function.Injective (value (rT := rT)) := by
  intro l k h
  have hr := congrArg (fun v : Val rT => root? v.fst) h
  simpa only [root_value, Option.some.injEq] using hr

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
/-- Recover the actual root after an observation through an alias. -/
theorem owns_root (l : Loc) (p : List Bool) :
    owns (value (rT := rT) l) p ⊢ UniformBag.owns l p := by
  iintro Hstate
  isimp only [owns] at Hstate
  ihave ⟨%k, %hk, Hbag⟩ := Hstate
  have hroot := value_injective hk
  subst k
  iframe Hbag

/-- Posterior-credit observation while retaining the explicit root location. -/
theorem twp_observe_root (E : CoPset) (l : Loc) (p : List Bool) (n : ℕ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(UniformBag.owns l p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      tglWp E pl(&(value (rT := rT) l).fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ q : List Bool,
          ⌜UniformBag.readRefines p n q ∧
            result = LatentReal.intervalVal (interval q n)⌝ ∗
          UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q F))) := by
  iintro ⟨Hbag, Hcredit⟩
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply twp_observe E (value l) p n F hF
    iframe Hcredit
    isimp only [owns]
    iexists l
    iframe Hbag
    itrivial
  iintro %result ⟨%q, %hq, Hstate, Hcredit⟩
  iexists q
  iframe Hcredit
  ihave Hbag := owns_root l q $$ Hstate
  iframe Hbag
  ipureintro
  exact hq

end specification

end SampLib.LatentUniform
