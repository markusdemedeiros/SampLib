import SampLib.Discrete.Laws.NegativeBinomialShape

/-! Endpoint, integer-shape, source-ratio, and infinite-credit checks for the rejection law. -/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.NegativeBinomialShape.ProducerCallers

noncomputable section

example (a : ℝ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) :
    (∫⁻ n, F n ∂law a ha 1 (by norm_num)) = F 0 := by
  rw [law_one]
  simp

example :
    (∫⁻ n, (if n = 0 then 0 else ∞ : ℝ≥0∞)
      ∂law (1 / 2) (by norm_num) 1 (by norm_num)) = 0 := by
  rw [law_one]
  simp

example (M n : ℕ) (hM : 0 < M) : ratio (M : ℝ) M n = 1 := by
  exact div_self (MultichooseSeries.pos (by exact_mod_cast hM : (0 : ℝ) < M) n).ne'

example : ratio (1 / 2) 1 2 = (3 / 8 : ℝ) := by
  calc
    _ = (PolyaEggenberger.rising 1 2 2 : ℝ) / PolyaEggenberger.rising 2 2 2 :=
      by simpa [ratio] using (rising_ratio_eq 1 2 1 2 (by norm_num) (by norm_num)).symm
    _ = _ := by norm_num [PolyaEggenberger.rising]

example : acceptanceMass (1 / 2) 1 1 = 1 := by simp [acceptanceMass]

example (a : ℝ) (ha : 0 < a) (p : unitInterval) (hp : 0 < (p : ℝ))
    (M : ℕ) (hM : 0 < M) (haM : a ≤ M) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ n, AcceptedProposal.kernel (NegativeBinomial.law p M) (acceptance a ha M hM haM)
      (accepted_mass_ne_zero a ha p hp M hM haM) F ε n ∂NegativeBinomial.law p M) ≤
      (∫⁻ n, F n ∂law a ha p hp) + ε :=
  conservation a ha p hp M hM haM F ε

#print axioms MultichooseSeries.hasSum
#print axioms MultichooseSeries.tsum_pmf
#print axioms integer_law_eq
#print axioms rising_ratio_eq
#print axioms weighted_expectation
#print axioms accepted_law_eq
#print axioms conservation
#print axioms law_one

end

end SampLib.NegativeBinomialShape.ProducerCallers
