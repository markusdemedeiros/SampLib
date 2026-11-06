import SampLib.ListEncoding
import SampLib.Samplers.RealCoin
import Samplers.Combinatorial.Permutations

/-! # Independent bit flips

Each input position is toggled by a fresh Bernoulli draw. The output retains the
input order and its full joint law, including deterministic endpoint biases.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FlipBits

noncomputable section

def flip (x c : Bool) : Bool := if c then !x else x

private theorem bool_rec_not (x : Bool) : Bool.rec true false x = !x := by
  cases x <;> rfl

section mathematics

open MeasureTheory

/-- Independent Bernoulli toggles applied to the fixed input bits. -/
def law (p : unitInterval) : List Bool → Measure (List Bool)
  | [] => Measure.dirac []
  | x :: xs => ((RealCoin.law p).prod (law p xs)).map
      (fun z => flip x z.1 :: z.2)

instance (p : unitInterval) (xs : List Bool) : IsProbabilityMeasure (law p xs) := by
  induction xs with
  | nil => dsimp [law]; infer_instance
  | cons x xs IH =>
    let := IH
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Conditional credit after the first toggle. -/
def credit (p : unitInterval) (x : Bool) (xs : List Bool)
    (F : List Bool → ℝ≥0∞) (c : Bool) : ℝ≥0∞ :=
  ∫⁻ ys, F (flip x c :: ys) ∂law p xs

/-- Independence separates the first toggle from the remaining bit flips. -/
theorem expectation (p : unitInterval) (x : Bool) (xs : List Bool)
    (F : List Bool → ℝ≥0∞) :
    ∫⁻ c, credit p x xs F c ∂RealCoin.law p = ∫⁻ ys, F ys ∂law p (x :: xs) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end mathematics

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : Bool) (xs : List Bool) :
    pl(inr((#bool x, {Exp.ofVal (listVal Val.bool xs)}))) =
      Exp.ofVal (listVal Val.bool (x :: xs) : Val rT) := by
  simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_flipBits (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Bool) (F : List Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law p xs) -∗
      tglWp E pl(&Occil.flipBits &(listVal Val.bool xs).fst &coin.fst)
        (fun v : Val rT => iprop(∃ ys : List Bool,
          ⌜v = listVal Val.bool ys⌝ ∗ ↯ (F ys))) := by
  induction xs generalizing F with
  | nil =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | cons x xs IH =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [← expectation p x xs F] at Hcredit
    iapply (hcoin.wp (credit p x xs F) (measurable_of_countable _) _) $$ Hcredit
    iintro %c Hcredit
    cases c
    · iterate 4 twp_pure
      twp_bind pl(&Occil.flipBits &(listVal Val.bool xs).fst &coin.fst)
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [credit, flip, Bool.false_eq_true, ite_false] at Hcredit
        iapply (IH (fun ys => F (x :: ys))) $$ Hcredit
      iintro %v ⟨%ys, %hv, Hcredit⟩
      subst v
      rw [encode_cons]
      iapply (tglWp_value (v := listVal Val.bool (x :: ys)))
      iexists x :: ys
      iframe Hcredit
      ipureintro
      exact Val.ext rfl
    · iterate 5 twp_pure
      twp_bind pl(&Occil.flipBits &(listVal Val.bool xs).fst &coin.fst)
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [credit, flip, ite_true] at Hcredit
        iapply (IH (fun ys => F ((!x) :: ys))) $$ Hcredit
      iintro %v ⟨%ys, %hv, Hcredit⟩
      subst v
      rw [encode_cons, bool_rec_not]
      iapply (tglWp_value (v := listVal Val.bool ((!x) :: ys)))
      iexists (!x) :: ys
      iframe Hcredit
      ipureintro
      exact Val.ext rfl

theorem flipBits_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Bool) :
    IsDistSpec (GF := GF) E pl(&Occil.flipBits &(listVal Val.bool xs).fst &coin.fst)
      (law p xs) (listVal Val.bool) where
  spec F _ := wand_entails (twp_flipBits E p coin hcoin xs F)

end specification

end

end SampLib.FlipBits
