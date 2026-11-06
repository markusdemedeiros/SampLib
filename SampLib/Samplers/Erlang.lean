import SampLib.Samplers.Exponential

/-! # Erlang sampling by independent unit-exponential sums -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Erlang

noncomputable section

section mathematics

open MeasureTheory Measure

private instance : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one

/-- The law with positive shape `n + 1`: the sum of `n + 1` unit exponentials. -/
def law : ℕ → Measure ℝ
  | 0 => ProbabilityTheory.expMeasure 1
  | n + 1 => ((law n).prod (ProbabilityTheory.expMeasure 1)).map
      (fun z : ℝ × ℝ => z.2 + z.1)

@[simp] theorem law_zero : law 0 = ProbabilityTheory.expMeasure 1 := rfl

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => unfold law; infer_instance
  | succ n ih =>
    have := ih
    unfold law
    infer_instance

/-- Conditional credit after the recursively sampled partial sum. -/
def credit (F : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, F (x + y) ∂ProbabilityTheory.expMeasure 1

theorem measurable_credit (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit F) :=
  (hF.comp (measurable_snd.add measurable_fst)).lintegral_prod_right'

/-- Exponential convolution gives the successive expectations in evaluation order. -/
theorem expectation_preservation (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, credit F y ∂law n = ∫⁻ z, F z ∂law (n + 1) := by
  have hadd : Measurable (fun z : ℝ × ℝ => z.2 + z.1) :=
    measurable_snd.add measurable_fst
  rw [law, lintegral_map hF hadd]
  exact (lintegral_prod _ (hF.comp hadd).aemeasurable).symm

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE specification for every positive integer shape, represented as `n + 1`. -/
theorem twp_erlang (E : CoPset) (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law n) -∗ tglWp E pl(&Occil.erlang #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  have hexp := Exponential.exponential_distSpec (GF := GF) E
  dsimp only [Exponential.law] at hexp
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pure
    simp only [Exponential.exponential_closeRec, Exponential.exponential_openRec]
    iterate 5 twp_pure
    simp only [Exponential.exponential_openRec]
    isimp only [law] at Hcredit
    iapply hexp.spec F hF $$ Hcredit
  | succ n ih =>
    iintro Hcredit
    twp_pure
    simp only [Exponential.exponential_closeRec, Exponential.exponential_openRec]
    iterate 5 twp_pure
    simp only [Exponential.exponential_openRec]
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.erlang #int ((n + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (ih (credit F) (measurable_credit F hF))
      isimp only [← expectation_preservation n F hF] at Hcredit
      iexact Hcredit
    iintro %v ⟨%y, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.exponential #())
    isimp only [credit] at Hcredit
    iapply (hexp.wp (fun x => F (x + y)) (hF.comp (measurable_id.add_const y)) _) $$ Hcredit
    iintro %x Hcredit
    twp_pures
    twp_value
    imodintro
    iexists (x + y)
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)

/-- Typed Erlang specification for every positive integer shape. -/
theorem erlang_distSpec (E : CoPset) (shape : ℕ) (hshape : 0 < shape) :
    IsDistSpec (GF := GF) E pl(&Occil.erlang #int (shape : ℤ))
      (law (shape - 1)) Val.real where
  spec F hF := by
    have h := twp_erlang (GF := GF) E (shape - 1) F hF
    rw [Nat.sub_add_cancel hshape] at h
    exact wand_entails h

end specification

end

end SampLib.Erlang
