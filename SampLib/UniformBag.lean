import SampLib.Distributions.DyadicPosterior
import SampLib.Samplers.FairCoin
import Samplers.Lazy

/-! # Cached uniform bags

The owned linked list records exactly the bits already sampled, ending in an
unsampled node. Continuation credits use the corresponding dyadic posterior.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

theorem uniformBagStep_lc {rT : Type} :
    (Occil.uniformBagStep : Exp rT).IsLocallyClosed := by is_lc

private theorem uniformBagStep_fv {rT : Type} :
    (Occil.uniformBagStep : Exp rT).fv = ∅ := by
  simp [Occil.uniformBagStep, Occil.newUniformBag, Occil.fairCoin, Exp.fv]

@[simp] theorem uniformBagStep_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.uniformBagStep = Occil.uniformBagStep :=
  (Exp.open_lc k e _ uniformBagStep_lc).symm

@[simp] theorem uniformBagStep_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.uniformBagStep : Exp rT) = Occil.uniformBagStep :=
  Exp.closeRec_fresh x _ k (by simp [uniformBagStep_fv])

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- An unsampled node contains the left injection of unit. -/
def emptyVal : Val rT := .inl .unit

/-- A sampled node contains its cached bit and the location of its tail. -/
def nodeVal (b : Bool) (tail : Loc) : Val rT := .inr (.pair (.bool b) (.loc tail))

/-- A finite cached prefix, followed by an owned unsampled cell. -/
def owns (l : Loc) : List Bool → IProp GF
  | [] => appHeapFrag l emptyVal
  | b :: p => iprop(∃ tail : Loc, appHeapFrag l (nodeVal b tail) ∗ owns tail p)

end ownership

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Allocation returns ownership of the actual fresh cell. -/
theorem twp_newUniformBag (E : CoPset) :
    ⊢ tglWp E pl(&Occil.newUniformBag #())
      (fun v : Val rT => iprop(∃ l : Loc, ⌜v = Val.loc l⌝ ∗ owns l [])) := by
  twp_pures
  change ⊢ tglWp E (.alloc (.ofVal (emptyVal : Val rT))) _
  iapply twp_alloc
  iintro %l Hl
  iexists l
  isimp only [owns]
  iframe Hl

/-- A step either reads the cached head or creates precisely one new cached bit. -/
def stepRefines (p : List Bool) (b : Bool) (q : List Bool) : Prop :=
  (p = [] ∧ q = []) ∨ p = b :: q

private theorem fresh_credit (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ b, DyadicPosterior.credit [b] F ∂RealCoin.law VonNeumann.fairBias) =
      DyadicPosterior.credit [] F := by
  rw [← FairCoin.expectation]
  simpa [Finset.sum_range_succ, add_comm] using
    (DyadicPosterior.credit_split [] F hF).symm

/-- The fresh-node kernel exposes the fair draw and all its heap resources. -/
theorem twp_freshStep (E : CoPset) (l : Loc) (K : Bool → ℝ≥0∞) :
    iprop(owns l [] ∗ ↯ (∫⁻ b, K b ∂RealCoin.law VonNeumann.fairBias)) ⊢
      tglWp E pl(&Occil.uniformBagStep #loc l)
        (fun v : Val rT => iprop(∃ (b : Bool) (tail : Loc),
          ⌜v = Val.pair (Val.bool b) (Val.loc tail)⌝ ∗
          appHeapFrag l (nodeVal b tail) ∗ owns tail [] ∗ ↯ (K b))) := by
  iintro ⟨Hl, Hcredit⟩
  isimp only [owns] at Hl
  twp_pures
  twp_bind pl(!#loc l)
  iapply twp_load
  iframe Hl
  iintro Hl
  twp_pures
  twp_bind (Exp.alloc (Exp.ofVal (emptyVal : Val rT)))
  iapply twp_alloc
  iintro %tail Htail
  simp only [FairCoin.fairCoin_openRec, FairCoin.fairCoin_closeRec]
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  iapply ((FairCoin.fairCoin_distSpec E).wp
    K (measurable_of_finite _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  twp_bind (Exp.store pl(#loc l) (Exp.ofVal (nodeVal b tail)))
  iapply twp_store
  iframe Hl
  iintro Hl
  twp_pures
  twp_value
  imodintro
  iexists b, tail
  isimp only [owns]
  iframe Hl Htail Hcredit

/-- Posterior-credit rule for a memoized step. The head cell remains owned. -/
theorem twp_uniformBagStep (E : CoPset) (l : Loc) (p : List Bool)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      tglWp E pl(&Occil.uniformBagStep #loc l)
        (fun v : Val rT => iprop(∃ (b : Bool) (tail : Loc) (q : List Bool),
          ⌜v = Val.pair (Val.bool b) (Val.loc tail) ∧ stepRefines p b q⌝ ∗
          appHeapFrag l (nodeVal b tail) ∗ owns tail q ∗
          ↯ (DyadicPosterior.credit (b :: q) F))) := by
  cases p with
  | nil =>
    iintro ⟨Hl, Hcredit⟩
    iapply tglWp_wand
    isplitl [Hl Hcredit]
    · iapply twp_freshStep E l (fun b => DyadicPosterior.credit [b] F)
      rw [fresh_credit F hF]
      iframe Hl Hcredit
    iintro %v ⟨%b, %tail, %hv, Hl, Htail, Hcredit⟩
    iexists b, tail, []
    iframe Hl Htail Hcredit
    ipureintro
    exact ⟨hv, Or.inl ⟨rfl, rfl⟩⟩
  | cons b p =>
    iintro ⟨Hbag, Hcredit⟩
    isimp only [owns] at Hbag
    ihave ⟨%tail, Hl, Htail⟩ := Hbag
    twp_pures
    twp_bind pl(!#loc l)
    iapply twp_load
    iframe Hl
    iintro Hl
    twp_pures
    twp_value
    imodintro
    iexists b, tail, p
    iframe Hl Htail Hcredit
    ipureintro
    exact ⟨rfl, Or.inr rfl⟩

end specification

end SampLib.UniformBag
