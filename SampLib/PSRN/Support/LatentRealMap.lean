import SampLib.Latent.LatentSpec
import Samplers.PSRN.Arithmetic

/-! # Deterministic transformations of deferred real draws

Mapping changes the represented value and its enclosure error, while retaining
one posterior on the original joint latent space. In particular, it never turns
aliases of an oracle into independent draws.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

open MeasureTheory

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Negation changes neither the shared state nor the interval error. -/
def negate (D : Model Ω S) : Model Ω S :=
  { D with value := fun x => -D.value x, measurable_value := D.measurable_value.neg }

/-- Scaling an oracle scales its error, not the underlying latent draw. -/
def scale (D : Model Ω S) (c : ℝ) : Model Ω S :=
  { D with
    value := fun x => D.value x * c
    measurable_value := D.measurable_value.mul_const c
    error := fun n x => D.error n x * |c|
    error_tendsto := fun s => (D.error_tendsto s).mono fun _ hx => by
      simpa using hx.mul_const |c| }

theorem scale_law (D : Model Ω S) (c : ℝ) (s : S) :
    (D.scale c).law s = (D.law s).map (fun x => x * c) := by
  rw [law, law, Measure.map_map
    (show Measurable (fun x : ℝ => x * c) by fun_prop) D.measurable_value]
  rfl

/-- Negating an observed interval preserves every fact about the same latent draw. -/
theorem encloses_negate (D : Model Ω S) {s : S} {n : ℕ} {I : RationalInterval}
    (hI : D.Encloses s n I) : D.negate.Encloses s n I.negate := by
  exact hI.mono fun _ hx => ⟨I.contains_negate hx.1, by
    simpa only [negate, RationalInterval.lowerReal_negate,
      RationalInterval.upperReal_negate, neg_sub_neg] using hx.2⟩

end Model

/-- Structural binders keep an arbitrary source value out of named-variable closing. -/
private def negateCode {rT : Type} (source : Exp rT) : Exp rT :=
  .lam (.app (.lam (.app (.lam
    (.pair (.unop .minus (.fst (.bvar 0)))
      (.pair (.unop .minus (.fst (.bvar 1))) (.snd (.bvar 0)))))
    (.snd (.bvar 0)))) (.app source (.bvar 0)))

/-- The oracle closure returned by the actual `PSRN.negate` constructor. -/
def negateVal {rT : Type} (source : Val rT) : Val rT :=
  ⟨negateCode source.fst, .lam (by
    apply Exp.lcb_imp_lc
    have hs (n : ℕ) : Exp.lcb n source.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le n)
    simp [Exp.lcb, hs]), by
    apply Exp.lcb_imp_lc
    have hs (n : ℕ) : Exp.lcb n source.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le n)
    simp [negateCode, Exp.lcb, hs]⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The transformed closure owns exactly its original oracle state. -/
def negateOwns (owns : Val rT → S → IProp GF) (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ source : Val rT, ⌜v = negateVal source⌝ ∗ owns source s)

/-- Negating an oracle only constructs a closure; it performs no observation. -/
theorem twp_negate (E : CoPset) (owns : Val rT → S → IProp GF)
    (source : Val rT) (s : S) :
    iprop(owns source s) ⊢
      tglWp E pl(&Occil.PSRN.negate &source.fst)
        (fun v => negateOwns owns v s) := by
  iintro Hstate
  twp_pures
  twp_value
  imodintro
  isimp only [negateOwns]
  iexists source
  iframe Hstate
  ipureintro
  apply Val.ext
  simp [negateVal, negateCode]

/-- A transformed read uses the original oracle's joint posterior credit. -/
theorem negate_oracleSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D owns) :
    IsOracleSpec E D.negate (negateOwns owns) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [negateOwns] at Hstate
    icases Hstate with ⟨%source, %hsourceVal, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&source.fst #int (n : ℤ))
    isimp only [Model.negate] at Hcredit
    iapply hsource.wp source s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    iexists t
    iexists I.negate
    isplit
    · ipureintro
      refine ⟨?_, hI.1, D.encloses_negate hI.2⟩
      apply Val.ext
      rfl
    isplitl [Hstate]
    · isimp only [negateOwns]
      iexists source
      iframe Hstate
      itrivial
    isimp only [Model.negate]
    iframe Hcredit

end specification

end

end SampLib.LatentReal
