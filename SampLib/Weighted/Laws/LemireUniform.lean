import SampLib.Weighted.Laws.MultiplyHigh
import SampLib.Uniform.Laws.UniformInt

/-! # Expectation for Lemire's multiply-high reduction

Equal accepted fibres give the uniform quotient law. The rejected low words fund
the retry with doubled credit.
-/

open MeasureTheory Finset
open scoped ENNReal

namespace SampLib.LemireUniform

noncomputable section

/-- A raw word pays its quotient on acceptance and the target plus doubled slack on
rejection. -/
def kernel (n width : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (r : ℕ) : ℝ≥0∞ :=
  if n * r % width < width % n then (∫⁻ y, F y ∂UniformInt.law n) + 2 * ε
  else F (n * r / width)

/-- Equal accepted fibres preserve the target expectation and finance retries. -/
theorem expectation (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ r, kernel n width F ε r ∂UniformInt.law width ≤
      (∫⁻ y, F y ∂UniformInt.law n) + ε := by
  let C := ∫⁻ y, F y ∂UniformInt.law n
  let q := width / n
  let t := width % n
  have hq : 0 < q := Nat.div_pos hnw hn
  have ht : t < n := Nat.mod_lt width hn
  have heq : t + n * q = width := Nat.mod_add_div width n
  have hnq : n ≤ n * q := by nlinarith
  have hwp : 0 < width := lt_of_lt_of_le hn hnw
  have hw : (width : ℝ≥0∞) ≠ 0 := by positivity
  have hwt : (width : ℝ≥0∞) ≠ ∞ := by finiteness
  have hreject : ((range width).filter
      (fun r => ¬width % n ≤ n * r % width)).card = t := by
    have hp := card_filter_add_card_filter_not (s := range width)
      (p := fun r => width % n ≤ n * r % width)
    rw [← MultiplyHigh.accepted, MultiplyHigh.card_accepted n width hn hnw,
      card_range] at hp
    dsimp [q] at heq
    omega
  have hsum : ∑ r ∈ range width, kernel n width F ε r =
      q * (∑ y ∈ range n, F y) + t * (C + 2 * ε) := by
    rw [← sum_filter_add_sum_filter_not (range width)
      (fun r => width % n ≤ n * r % width)]
    have hfirst : ∑ r ∈ MultiplyHigh.accepted n width, kernel n width F ε r =
        q * ∑ y ∈ range n, F y := by
      calc
        _ = ∑ r ∈ MultiplyHigh.accepted n width, F (n * r / width) :=
          sum_congr rfl fun r hr => by
            exact ite_eq_right (Nat.not_lt.mpr (mem_filter.mp hr).2)
        _ = _ := MultiplyHigh.sum_accepted n width hn hnw F
    rw [← MultiplyHigh.accepted, hfirst]
    have hlast : ∑ r ∈ (range width).filter
        (fun r => ¬width % n ≤ n * r % width), kernel n width F ε r =
          t * (C + 2 * ε) := by
      calc
        _ = ∑ _r ∈ (range width).filter
            (fun r => ¬width % n ≤ n * r % width), (C + 2 * ε) :=
          sum_congr rfl fun r hr => by
            simp only [kernel, C, ite_eq_left (Nat.lt_of_not_ge (mem_filter.mp hr).2)]
        _ = _ := by simp only [sum_const, nsmul_eq_mul, hreject]
    rw [hlast]
  have hcredit : (∑ y ∈ range n, F y) = n * C := by
    rw [show C = (∑ y ∈ range n, F y) / n from UniformInt.lintegral_law n F,
      ENNReal.mul_div_cancel (by positivity) (by finiteness)]
  have hparts : ((n * q : ℕ) + (t : ℝ≥0∞)) / width = 1 := by
    rw [← Nat.cast_add, Nat.add_comm (n * q) t, heq, ENNReal.div_self hw hwt]
  have hretry : ((2 * t : ℕ) : ℝ≥0∞) / width ≤ 1 := by
    rw [ENNReal.div_le_iff hw hwt, one_mul]
    exact_mod_cast (show 2 * t ≤ width by omega)
  rw [UniformInt.lintegral_law]
  calc
    _ = (((n * q : ℕ) + (t : ℝ≥0∞)) / width) * C +
        (((2 * t : ℕ) : ℝ≥0∞) / width) * ε := by
      rw [hsum, hcredit]
      simp only [Nat.cast_mul, Nat.cast_ofNat, ENNReal.div_eq_inv_mul]
      ring
    _ ≤ C + ε := by
      rw [hparts, one_mul]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hretry)

end

end SampLib.LemireUniform
