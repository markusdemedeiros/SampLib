import SampLib.Samplers.Zipf

open ProbLang
open scoped ENNReal

example : SampLib.Zipf.law 3 0 2 (by decide) {(1 : Fin 3)} = (1 : ℝ≥0∞) / 3 := by
  rw [SampLib.Zipf.law_zero, SampLib.UniformFin.law_singleton]
  norm_num [ENNReal.div_eq_inv_mul]

example : SampLib.Zipf.law 1 5 3 (by decide) {(0 : Fin 1)} = 1 := by
  rw [SampLib.Zipf.law_one]
  simp

example (n a b : ℕ) [NeZero n] (hb : 0 < b) (k : Fin n) :
    SampLib.Zipf.law n a b hb {k} =
      ENNReal.ofReal (((k : ℕ) + 1 : ℝ) ^ (-((a : ℝ) / b))) /
        SampLib.Zipf.normalizer n a b hb := by
  rw [SampLib.Zipf.law_singleton, SampLib.Zipf.weight_eq]

#print axioms SampLib.Zipf.law_singleton
#print axioms SampLib.Zipf.expectation
#print axioms SampLib.Zipf.zipf_distSpec

section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n a b : ℕ) [NeZero n] (hb : 0 < b) (F : Fin n → ℝ≥0∞)
    (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂SampLib.Zipf.law n a b hb) -∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.zipf #int (n : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v => iprop(∃ (k : Fin n), ⌜v = Val.int (k + 1 : ℕ)⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro Hcredit HR
  iapply ((SampLib.Zipf.zipf_distSpec E n a b hb).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

example (E : CoPset) (n a b : ℕ) [NeZero n] (hb : 0 < b) :
    ⊢ ↯ (∞ : ℝ≥0∞) -∗
      tglWp E pl(&Occil.DiscreteExtra.zipf #int (n : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v => iprop(∃ (k : Fin n), ⌜v = Val.int (k + 1 : ℕ)⌝ ∗ ↯ (∞ : ℝ≥0∞))) := by
  have h := (SampLib.Zipf.zipf_distSpec (rT := rT) (GF := GF) E n a b hb).spec
    (fun _ => ∞) measurable_const
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one] at h
  iintro Hcredit
  iapply h $$ Hcredit

end
