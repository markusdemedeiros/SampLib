import SampLib.Discrete.Laws.Wallenius
import SampLib.Common.Laws.Urn

/-! # Two-color Wallenius law

With two colors, the weighted choice of the first color is a rational coin.
The marked count then has the urn recurrence of the source sampler.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.Wallenius

noncomputable section

/-- A two-color urn returns the number of marked-color draws. -/
def twoColorLaw (n ones zeros a b : ℕ) : Measure ℕ :=
  (law n [ones, zeros] [a, b]).map (fun ys => ys[0]?.getD 0)

instance (n ones zeros a b : ℕ) : IsProbabilityMeasure (twoColorLaw n ones zeros a b) where
  measure_univ := by
    rw [twoColorLaw, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- The marked count is the number of zeros in the canonical two-color word. -/
theorem twoColor_word (n ones zeros a b : ℕ) :
    twoColorLaw n ones zeros a b =
      (wordLaw [ones, zeros] [a, b] n).map (fun word => word.count 0) := by
  rw [twoColorLaw, law, Measure.map_map
    (measurable_of_countable _) (measurable_of_countable _)]
  congr 1

@[simp] theorem twoColor_zero (ones zeros a b : ℕ) :
    twoColorLaw 0 ones zeros a b = Measure.dirac 0 := by
  rw [twoColor_word, wordLaw, Measure.map_dirac' (measurable_of_countable _)]
  simp

private theorem twoColor_lintegral (n ones zeros a b : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂twoColorLaw n ones zeros a b =
      ∫⁻ word, F (word.count 0) ∂wordLaw [ones, zeros] [a, b] n := by
  rw [twoColor_word, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]

/-- A two-category proportional draw is the corresponding marked-color coin. -/
theorem coin_categorical (u v : ℕ) (hs : 0 < u + v) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, F (if b then 0 else 1) ∂RealCoin.law (Urn.bias u v) =
      ∫⁻ i, F i ∂WeightedChoice.law [u, v] := by
  rw [RealCoin.lintegral_law, RealCoin.credit, Urn.pmf_true u v hs,
    Urn.pmf_false u v hs, WeightedChoice.lintegral_law]
  simp [WeightedChoice.weightedSum, ENNReal.div_eq_inv_mul]
  ring

/-- The coin only selects colors that still contain a ball. -/
theorem coin_selected (ones zeros a b : ℕ) (hs : 0 < ones * a + zeros * b) :
    ∀ᵐ marked ∂RealCoin.law (Urn.bias (ones * a) (zeros * b)),
      if marked then 0 < ones else 0 < zeros := by
  apply ae_iff_of_countable.mpr
  intro marked hm
  cases marked with
  | false =>
    change 0 < zeros
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    apply hm
    have hp : RealCoin.pmf (Urn.bias (ones * a) (zeros * b)) false = 0 := by
      rw [Urn.pmf_false (ones * a) (zeros * b) hs]
      simp [hz]
    simpa [RealCoin.law] using hp
  | true =>
    change 0 < ones
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    apply hm
    have hp : RealCoin.pmf (Urn.bias (ones * a) (zeros * b)) true = 0 := by
      rw [Urn.pmf_true (ones * a) (zeros * b) hs]
      simp [hz]
    simpa [RealCoin.law] using hp

/-- The two-color first-draw expectation includes empty colors and arbitrary infinite credits. -/
theorem twoColor_expectation (n ones zeros a b : ℕ) (hn : n + 1 ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) (F : ℕ → ℝ≥0∞) :
    ∫⁻ marked, (if marked then
        ∫⁻ k, F (k + 1) ∂twoColorLaw n (ones - 1) zeros a b
      else ∫⁻ k, F k ∂twoColorLaw n ones (zeros - 1) a b)
      ∂RealCoin.law (Urn.bias (ones * a) (zeros * b)) =
        ∫⁻ k, F k ∂twoColorLaw (n + 1) ones zeros a b := by
  have hodds : ∀ o ∈ [a, b], 0 < o := by simp [ha, hb]
  have hsWord := request_weight_pos [ones, zeros] [a, b] n (by simpa using hn) rfl hodds
  have hs : 0 < ones * a + zeros * b := by simpa [weights] using hsWord
  let K (i : ℕ) := ∫⁻ word, F ((i :: word).count 0)
    ∂wordLaw (decrement [ones, zeros] i) [a, b] n
  have hbranch (marked : Bool) :
      (if marked then ∫⁻ k, F (k + 1) ∂twoColorLaw n (ones - 1) zeros a b
        else ∫⁻ k, F k ∂twoColorLaw n ones (zeros - 1) a b) =
      K (if marked then 0 else 1) := by
    cases marked <;> simp [K, twoColor_lintegral, decrement]
  calc
    _ = ∫⁻ marked, K (if marked then 0 else 1)
        ∂RealCoin.law (Urn.bias (ones * a) (zeros * b)) :=
      lintegral_congr_ae (Filter.Eventually.of_forall hbranch)
    _ = ∫⁻ i, K i ∂WeightedChoice.law (weights [ones, zeros] [a, b]) :=
      coin_categorical (ones * a) (zeros * b) hs K
    _ = _ := by
      rw [twoColor_lintegral]
      exact word_expectation [ones, zeros] [a, b] n hsWord (fun word => F (word.count 0))

end

end SampLib.Wallenius
