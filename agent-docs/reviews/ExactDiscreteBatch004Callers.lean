import SampLib.Discrete.BinomialHalfRejection

open ProbLang
open scoped ENNReal

namespace ReviewExactDiscrete004

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (n : ℕ) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Binomial.law VonNeumann.fairBias n) ∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfRejection #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (BinomialHalfRejection.binomialHalfRejection_distSpec E n).wp
    F (measurable_of_countable _) _ $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 0 F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 1 F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 2 F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 3 F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 4 F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 5 F R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) := framed E 6 F R
example (E : CoPset) (R : IProp GF) := framed E 4 (fun _ => ∞) R
example (E : CoPset) (R : IProp GF) := framed E 5 (fun _ => ∞) R

private theorem width_four : BinomialHalfEnvelope.width 4 = 3 := by
  norm_num [BinomialHalfEnvelope.width]
example : BinomialHalfEnvelope.width 6 = 3 := by
  norm_num [BinomialHalfEnvelope.width]

/-- Every even rejection proposal has total accepted mass exactly1/16. -/
example : (∫⁻ t, ENNReal.ofReal (BinomialHalfProposal.acceptance 4 t)
    ∂BinomialHalfProposal.law 4) = (1 : ℝ≥0∞) / 16 := by
  simpa using BinomialHalfProposal.accepted_expectation 4 (by decide) (fun _ => 1)

/-- Center and reflected endpoint proposals are distinct and inside the support. -/
example : BinomialHalfProposal.candidate 4 (0, ⟨0, by rw [width_four]; decide⟩, true) = 2 := by
  norm_num [BinomialHalfProposal.candidate, width_four]
example : BinomialHalfProposal.candidate 4 (0, ⟨1, by rw [width_four]; decide⟩, false) = 0 := by
  norm_num [BinomialHalfProposal.candidate, width_four]
example : BinomialHalfProposal.acceptance 4 (1, ⟨0, by rw [width_four]; decide⟩, true) = 0 := by
  norm_num [BinomialHalfProposal.acceptance, BinomialHalfProposal.candidate, width_four]

example : Binomial.law VonNeumann.fairBias 4 {5} = 0 := by
  rw [Binomial.law_singleton]
  simp

example : Binomial.law VonNeumann.fairBias 0 {0} = 1 := by
  rw [Binomial.law_singleton]
  simp

#print axioms SampLib.BinomialHalfRejection.binomialHalfRejection_distSpec
#print axioms SampLib.BinomialHalfProposal.accepted_expectation
#print axioms SampLib.BinomialHalfProposal.expectation
#print axioms SampLib.BinomialHalfEnvelope.acceptance_bound
#print axioms SampLib.IntegerSqrt.twp_integerSqrt
#print axioms framed

end
end ReviewExactDiscrete004
