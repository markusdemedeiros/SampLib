import SampLib.Discrete.Laws.NegativeBinomialShape
import SampLib.Discrete.Laws.NegativeBinomial
import SampLib.Uniform.Laws.RationalCoin

/-! # Rational-shape negative binomial by rejection

The proposal is the integer negative binomial with shape `M = ⌈A/B⌉`. A count `k`
is accepted with the rising-product ratio `∏_{i<k} (A + iB) / ((M + i)B)`, which
cancels the proposal's multichoose coefficient. The accepted-proposal identity
preserves every continuation credit and pays for the retry amplification.
-/

open scoped ENNReal

namespace SampLib.PolyaRational

noncomputable section

open PolyaEggenberger (rising)

/-- The source's integer ceiling of the target shape `A/B`. -/
def ceiling (A B : ℕ) : ℕ := (A + B - 1) / B

theorem ceiling_pos (A B : ℕ) (hA : 0 < A) (hB : 0 < B) : 0 < ceiling A B :=
  Nat.div_pos (by omega) hB

theorem le_ceiling (A B : ℕ) (hB : 0 < B) : A ≤ ceiling A B * B := by
  have h := Nat.lt_div_mul_add (a := A + B - 1) hB
  unfold ceiling
  omega

def shape (A B : ℕ) : ℝ := (A : ℝ) / B

theorem shape_pos (A B : ℕ) (hA : 0 < A) (hB : 0 < B) : 0 < shape A B := by
  unfold shape
  positivity

theorem shape_le (A B : ℕ) (hB : 0 < B) : shape A B ≤ ceiling A B := by
  unfold shape
  rw [div_le_iff₀ (by exact_mod_cast hB)]
  exact_mod_cast le_ceiling A B hB

/-- The success probability `s/t` of every proposal trial. -/
abbrev success (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) : unitInterval :=
  RationalCoin.bias s t (by omega) (by omega) (by exact_mod_cast hst)

theorem success_pos (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) : 0 < (success s t hs hst : ℝ) := by
  simp only [success, RationalCoin.bias, Int.cast_natCast]
  exact div_pos (by exact_mod_cast hs) (by exact_mod_cast lt_of_lt_of_le hs hst)

/-- The canonical negative binomial with shape `A/B` and success probability `s/t`. -/
abbrev law (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hst : s ≤ t) :=
  NegativeBinomialShape.law (shape A B) (shape_pos A B hA hB) (success s t hs hst)
    (success_pos s t hs hst)

section mathematics

open MeasureTheory

variable (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hst : s ≤ t)

abbrev acceptance : ℕ → unitInterval :=
  NegativeBinomialShape.acceptance (shape A B) (shape_pos A B hA hB) (ceiling A B)
    (ceiling_pos A B hA hB) (shape_le A B hB)

abbrev proposal : Measure ℕ := NegativeBinomial.law (success s t hs hst) (ceiling A B)

theorem mass_ne_zero :
    AcceptedProposal.mass (proposal A B s t hs hst) (acceptance A B hA hB) ≠ 0 :=
  NegativeBinomialShape.accepted_mass_ne_zero _ _ _ (success_pos s t hs hst) _ _ _

/-- Accept the proposed count or retain the amplified retry budget. -/
def branchCredit (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) (accepted : Bool) : ℝ≥0∞ :=
  if accepted then F k else
    (∫⁻ n, F n ∂law A B s t hA hB hs hst) +
      AcceptedProposal.factor (proposal A B s t hs hst) (acceptance A B hA hB) * ε

/-- Conditional expectation of the rising-product acceptance coin. -/
def proposalCredit (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  RealCoin.credit (acceptance A B hA hB k) (branchCredit A B s t hA hB hs hst F ε k)

/-- Rising-product weighting preserves the target expectation and the retry slack. -/
theorem expectation_preservation (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, proposalCredit A B s t hA hB hs hst F ε k ∂proposal A B s t hs hst) ≤
      (∫⁻ n, F n ∂law A B s t hA hB hs hst) + ε := by
  have hC : AcceptedProposal.credit (proposal A B s t hs hst) (acceptance A B hA hB)
      (mass_ne_zero A B s t hA hB hs hst) F = ∫⁻ n, F n ∂law A B s t hA hB hs hst := by
    rw [AcceptedProposal.credit, NegativeBinomialShape.accepted_law_eq]
  simpa only [proposalCredit, branchCredit, RealCoin.credit, RealCoin.pmf,
    ite_true, Bool.false_eq_true, ite_false, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, hC] using
    AcceptedProposal.expectation_preservation (proposal A B s t hs hst)
      (acceptance A B hA hB) (measurable_of_countable _)
      (mass_ne_zero A B s t hA hB hs hst) F (measurable_of_countable _) ε

include hA hB in
theorem bottom_pos (k : ℕ) : (0 : ℤ) < rising (ceiling A B * B) B k := by
  exact_mod_cast NegativeBinomialShape.rising_pos (Nat.mul_pos (ceiling_pos A B hA hB) hB) B k

include hB in
theorem top_le (k : ℕ) : (rising A B k : ℤ) ≤ rising (ceiling A B * B) B k := by
  exact_mod_cast NegativeBinomialShape.rising_mono (le_ceiling A B hB) B k

/-- The source's integer products give exactly the acceptance probability. -/
theorem ratio_bias (k : ℕ) :
    RationalCoin.bias (rising A B k) (rising (ceiling A B * B) B k) (by positivity)
      (bottom_pos A B hA hB k) (top_le A B hB k) = acceptance A B hA hB k := by
  apply Subtype.ext
  simp only [RationalCoin.bias, Int.cast_natCast, NegativeBinomialShape.acceptance]
  rw [NegativeBinomialShape.rising_ratio_eq A B (ceiling A B) k hB (ceiling_pos A B hA hB)]
  rfl

end mathematics

end

end SampLib.PolyaRational
