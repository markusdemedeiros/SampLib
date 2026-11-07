module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import SampLib.Discrete.Laws.UrnWaiting

@[expose] public section

/-! # Failure counts before successive marked draws in a reinforced urn

Condition on the waiting time to the first marked draw, then update the urn.
This finite convolution of proper waiting laws defines the inverse-urn law
independently of the sampler's recursive control flow.
-/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.InverseUrn

noncomputable section

/-- Failures before `r` marked draws, by successive first-marked waiting times. -/
def law : (r a b c : ℕ) → 0 < a → Measure ℕ
  | 0, _, _, _, _ => dirac 0
  | r + 1, a, b, c, ha => (UrnWaiting.law a b c).bind (fun n =>
      (law r (a + c) (b + n * c) c (by omega)).map (fun rest => n + rest))

instance (r a b c : ℕ) (ha : 0 < a) : IsProbabilityMeasure (law r a b c ha) := by
  induction r generalizing a b with
  | zero => dsimp [law]; infer_instance
  | succ r ih =>
    let := UrnWaiting.isProbabilityMeasure_law a b c ha
    have hnext (n : ℕ) : IsProbabilityMeasure
        ((law r (a + c) (b + n * c) c (by omega)).map (fun rest => n + rest)) := by
      let := ih (a + c) (b + n * c) (by omega)
      infer_instance
    constructor
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Expected output credit conditional on the first marked waiting time. -/
theorem first_wait_expectation (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law (r + 1) a b c ha =
      ∑' n, AbsorbingChain.mass (UrnWaiting.continuation a b c) 0 n *
        ∫⁻ rest, F (n + rest) ∂law r (a + c) (b + n * c) c (by omega) := by
  let := UrnWaiting.isProbabilityMeasure_law a b c ha
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp_rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rw [UrnWaiting.law, AbsorbingChain.lintegral_stopLaw]
  simp

/-- First-draw conditioning for the inverse urn: mark, or reinforce and shift. -/
theorem expectation (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law (r + 1) a b c ha =
      (1 - UrnWaiting.continuation a b c 0) *
        ∫⁻ k, F k ∂law r (a + c) b c (by omega) +
      UrnWaiting.continuation a b c 0 *
        ∫⁻ k, F (k + 1) ∂law (r + 1) a (b + c) c ha := by
  rw [first_wait_expectation, first_wait_expectation,
    tsum_eq_zero_add' ENNReal.summable, ← ENNReal.tsum_mul_left]
  simp only [AbsorbingChain.mass_zero, Nat.zero_add, Nat.zero_mul, Nat.add_zero]
  congr 1
  apply tsum_congr
  intro n
  rw [UrnWaiting.mass_succ, show b + (n + 1) * c = (b + c) + n * c by ring]
  rw [mul_assoc]
  congr 2
  apply lintegral_congr
  intro k
  congr 1
  omega

end

end SampLib.InverseUrn
