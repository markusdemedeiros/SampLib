import SampLib.Discrete.BinomialHalfRejection

open ProbLang
open scoped ENNReal

example : SampLib.BinomialHalfRejection.law 0 {0} = 1 := by
  simp [SampLib.BinomialHalfRejection.law, SampLib.Binomial.law]

example : SampLib.BinomialHalfRejection.law 4 {2} = (3 : ℝ≥0∞) / 8 := by
  rw [SampLib.BinomialHalfProposal.half_binomial_mass]
  norm_num [Nat.choose, ENNReal.ofReal_div_of_pos]

example : SampLib.BinomialHalfRejection.law 5 {2} = (5 : ℝ≥0∞) / 16 := by
  rw [SampLib.BinomialHalfProposal.half_binomial_mass]
  norm_num [Nat.choose, ENNReal.ofReal_div_of_pos]

#print axioms SampLib.BinomialHalfEnvelope.acceptance_bound
#print axioms SampLib.BinomialHalfProposal.accepted_expectation
#print axioms SampLib.BinomialHalfProposal.expectation
#print axioms SampLib.BinomialHalfRejection.binomialHalfRejection_distSpec

section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n : ℕ) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂SampLib.BinomialHalfRejection.law n) -∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ))
        (fun v => iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro Hcredit HR
  iapply ((SampLib.BinomialHalfRejection.binomialHalfRejection_distSpec E n).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

example (E : CoPset) (n : ℕ) :
    ⊢ ↯ (∞ : ℝ≥0∞) -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ))
        (fun v => iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (∞ : ℝ≥0∞))) := by
  have h := (SampLib.BinomialHalfRejection.binomialHalfRejection_distSpec
    (rT := rT) (GF := GF) E n).spec (fun _ => ∞) measurable_const
  simp only [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one] at h
  iintro Hcredit
  iapply h $$ Hcredit

end
