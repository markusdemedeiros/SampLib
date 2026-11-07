import SampLib.Discrete.Laws.InverseUrn
import SampLib.Common.Laws.Urn
import SampLib.Uniform.Laws.RealCoin

/-! # Inverse Pólya first-color recurrence

Each draw either completes the next required success or adds one failure. The
urn coin splits the expected credit along that first-color recurrence.
-/

open scoped ENNReal

namespace SampLib.InversePolya

noncomputable section

open MeasureTheory (lintegral_congr lintegral_dirac)

abbrev law := InverseUrn.law

/-- Continuation credit after the first color at failure depth `n`. -/
def kernel (exit : ℕ → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then exit n else c

/-- Credit remaining after the next marked draw, including previous failures. -/
def successCredit (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, F (n + k) ∂law r (a + c) (b + n * c) c
    (ha.trans_le (Nat.le_add_right a c))

private theorem coin_continuation (a b c n : ℕ) (ha : 0 < a) :
    RealCoin.pmf (Urn.bias a (b + n * c)) false = UrnWaiting.continuation a b c n := by
  have ht : 0 < a + (b + n * c) := by omega
  simp [Urn.bias, ht, RealCoin.pmf, RationalCoin.bias,
    UrnWaiting.continuation, UrnWaiting.hazard, Nat.cast_add, Nat.cast_mul, add_assoc]

/-- The marked branch receives the lower-success-count expectation. -/
theorem coin_expectation (a b c n : ℕ) (ha : 0 < a)
    (exit : ℕ → ℝ≥0∞) (credit : ℝ≥0∞) :
    ∫⁻ color, kernel exit n credit color ∂RealCoin.law (Urn.bias a (b + n * c)) =
      (1 - UrnWaiting.continuation a b c n) * exit n +
        UrnWaiting.continuation a b c n * credit := by
  have hstop : RealCoin.pmf (Urn.bias a (b + n * c)) true =
      1 - UrnWaiting.continuation a b c n := by
    rw [← coin_continuation a b c n ha]
    have h := RealCoin.pmf_sum (Urn.bias a (b + n * c))
    exact ENNReal.eq_sub_of_add_eq (by simp [RealCoin.pmf]) h
  simp [RealCoin.lintegral_law, RealCoin.credit, kernel,
    hstop, coin_continuation a b c n ha]

/-- The urn recurrence includes the accumulated failure count in its credit. -/
theorem expectation (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) (n : ℕ) :
    ∫⁻ k, F (n + k) ∂law (r + 1) a (b + n * c) c ha =
      (1 - UrnWaiting.continuation a b c n) *
        successCredit r a b c ha F n +
      UrnWaiting.continuation a b c n *
        ∫⁻ k, F (n + 1 + k) ∂law (r + 1) a (b + (n + 1) * c) c ha := by
  unfold successCredit
  rw [InverseUrn.expectation]
  have hq : UrnWaiting.continuation a (b + n * c) c 0 =
      UrnWaiting.continuation a b c n := by
    simp [UrnWaiting.continuation, UrnWaiting.hazard, Nat.cast_add, Nat.cast_mul, add_assoc]
  rw [hq, show b + (n + 1) * c = b + n * c + c by ring]
  congr 2
  apply lintegral_congr
  intro k
  congr 1
  omega

end

end SampLib.InversePolya
