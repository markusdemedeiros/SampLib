import SampLib.Constants.Laws.EulerSondow
import SampLib.Constants.Laws.PositiveSeries

/-! # The positive-series certificate used by Euler's constant coin

The getter computes binary length exactly. Its rational remainder is valid by
Sondow's dyadic-tail argument and vanishes even under the coarse bound `size n ≤ n`.
-/

open Finset

namespace SampLib.EulerMascheroniSeries

noncomputable section

def coefficient (n : ℕ) : FromPositiveSeries.Coefficient :=
  if hn : n = 0 then
    ⟨1, 2, by norm_num, 1, 2, by norm_num⟩
  else
    ⟨n.size, 2 * n * (2 * n + 1) * (2 * n + 2), by
      have : 0 < n := by omega
      positivity,
      (2 + n.size) * n + 1, 16 * n * n * n, by
      have : 0 < n := by omega
      positivity⟩

theorem coefficient_value (n : ℕ) : (coefficient n).value = EulerSondow.term n := by
  by_cases hn : n = 0
  · subst n
    norm_num [coefficient, FromPositiveSeries.Coefficient.value, EulerSondow.term]
  · simp [coefficient, hn, FromPositiveSeries.Coefficient.value,
      EulerSondow.term, EulerSondow.delta, div_eq_mul_inv]

theorem coefficient_error (n : ℕ) (hn : 1 ≤ n) :
    (coefficient n).error = (((2 + n.size) * n + 1 : ℕ) : ℝ) / (16 * (n : ℝ) ^ 3) := by
  have hz : n ≠ 0 := by omega
  simp only [coefficient, dite_eq_right hz, FromPositiveSeries.Coefficient.error]
  push_cast
  congr 1
  ring

private theorem remainder (n : ℕ) : Real.eulerMascheroniConstant ≤
    (∑ i ∈ range (n + 1), EulerSondow.term i) + (coefficient n).error := by
  by_cases hn : n = 0
  · subst n
    norm_num [EulerSondow.term, coefficient, FromPositiveSeries.Coefficient.error]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  · have hpos : 1 ≤ n := by omega
    have hsum := EulerSondow.hasSum_term.summable.sum_add_tsum_nat_add (n + 1)
    have ht := EulerSondow.weighted_tail_le n hpos
    have he : (fun k => EulerSondow.term (k + (n + 1))) =
        (fun k => ((k + (n + 1)).size : ℝ) * EulerSondow.delta (k + (n + 1))) := by
      funext k
      simp [EulerSondow.term]
    rw [he, EulerSondow.hasSum_term.tsum_eq] at hsum
    rw [coefficient_error n hpos]
    linarith

private theorem error_le_inv (n : ℕ) (hn : 1 ≤ n) : (coefficient n).error ≤ 1 / (n : ℝ) := by
  rw [coefficient_error n hn]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (n.size : ℝ) ≤ n := by
    exact_mod_cast (Nat.size_le.mpr n.lt_two_pow_self : n.size ≤ n)
  push_cast
  field_simp
  nlinarith [sq_nonneg (n : ℝ)]

/-- All data are the source's exact integer numerator/denominator tuples. -/
def parameters : FromPositiveSeries.Parameters where
  coefficient := coefficient
  summable := by simpa only [coefficient_value] using EulerSondow.hasSum_term.summable
  mass_le_one := by
    simp only [coefficient_value, EulerSondow.hasSum_term.tsum_eq]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  remainder n := by
    simpa only [coefficient_value, EulerSondow.hasSum_term.tsum_eq] using remainder n
  tight ε hε := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (1 / ε))
    have hn₁ : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
    have hn₂ : 1 / ε < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hnp : (0 : ℝ) < n := by linarith
    refine ⟨n, (error_le_inv n (by exact_mod_cast hn₁.le)).trans ?_⟩
    apply (div_le_iff₀ hnp).mpr
    have h := (div_lt_iff₀ hε).mp hn₂
    nlinarith

theorem bias_coe : (FromPositiveSeries.bias parameters : ℝ) = Real.eulerMascheroniConstant := by
  simp [FromPositiveSeries.bias, parameters, coefficient_value, EulerSondow.hasSum_term.tsum_eq]

end

end SampLib.EulerMascheroniSeries
