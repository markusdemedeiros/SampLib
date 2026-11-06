import SampLib.Templates
import Samplers.Continuous
import Metrology.Iris.LocalBI

/-! # Irwin–Hall sampling by independent unit-uniform sums -/

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.UniformSum

noncomputable section

section mathematics

open MeasureTheory Measure

/-- The `n`-fold convolution of the unit-uniform law, starting at zero. -/
def law : ℕ → Measure ℝ
  | 0 => dirac 0
  | n + 1 => (unifUnit.prod (law n)).map (fun z : ℝ × ℝ => z.1 + z.2)

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => unfold law; infer_instance
  | succ n ih =>
    have := ih
    unfold law
    infer_instance

/-- Conditional credit after the new uniform draw. -/
def credit (n : ℕ) (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, F (x + y) ∂law n

theorem measurable_credit (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit n F) :=
  (hF.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'

/-- Convolution expectation is the successive expectation of the two summands. -/
theorem expectation_preservation (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit n F x ∂unifUnit = ∫⁻ z, F z ∂law (n + 1) := by
  have hsum : Measurable (fun z : ℝ × ℝ => z.1 + z.2) :=
    measurable_fst.add measurable_snd
  rw [law, lintegral_map hF hsum]
  exact (lintegral_prod _ (hF.comp hsum).aemeasurable).symm

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE specification for every nonnegative number of uniforms. -/
theorem twp_uniformSum (E : CoPset) (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law n) -∗ tglWp E pl(&Occil.uniformSum #int (n : ℤ))
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists (0 : ℝ)
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)
  | succ n ih =>
    iintro Hcredit
    twp_pures
    twp_bind pl(urand)
    iapply (twp_urand_exp (measurable_credit n F hF) ?_) $$ Hcredit
    · rw [expectation_preservation n F hF]
    iintro %x ⟨_, Hcredit⟩
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.uniformSum #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [credit] at Hcredit
      iapply (ih (fun y => F (x + y)) (hF.comp (measurable_const.add measurable_id))) $$ Hcredit
    iintro %v ⟨%y, %hv, Hcredit⟩
    subst v
    twp_pures
    twp_value
    imodintro
    iexists (x + y)
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)

/-- Typed Irwin–Hall specification, including the zero-summand point mass. -/
theorem uniformSum_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.uniformSum #int (n : ℤ)) (law n) Val.real where
  spec F hF := wand_entails (twp_uniformSum E n F hF)

end specification

end

end SampLib.UniformSum
