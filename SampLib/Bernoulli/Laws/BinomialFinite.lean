import SampLib.Common.Laws.Binomial

/-! # The binomial law on its finite support

The count is at most the number of trials. Counts outside that range get a fallback credit,
so the finite sum equals the expectation for every extended-real continuation.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.BinomialFinite

noncomputable section

def pmf (p : unitInterval) (n : ℕ) (k : Fin (n + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ (k : ℕ) * (1 - (p : ℝ)) ^ (n - k))

def extend {n : ℕ} (fallback : ℝ≥0∞) (F : Fin (n + 1) → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if h : k ≤ n then F ⟨k, Nat.lt_succ_iff.mpr h⟩ else fallback

theorem expectation (p : unitInterval) (n : ℕ) (fallback : ℝ≥0∞)
    (F : Fin (n + 1) → ℝ≥0∞) :
    (∫⁻ k, extend fallback F k ∂Binomial.law p n) = ∑ k, pmf p n k * F k := by
  rw [Binomial.lintegral_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun k =>
      ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) *
        extend fallback F k) (n + 1)]
  apply sum_congr rfl
  intro k _
  simp only [extend, dite_eq_left (Nat.le_of_lt_succ k.isLt), pmf]

theorem pmf_sum (p : unitInterval) (n : ℕ) : ∑ k, pmf p n k = 1 := by
  have h := expectation p n 1 (fun _ => 1)
  simpa [extend] using h.symm

end

end SampLib.BinomialFinite
