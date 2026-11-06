import SampLib.Distributions.Multinomial
import SampLib.Distributions.WeightedSupport

/-! One categorical trial increments the canonical multinomial count vector. -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.WeightedChoice

/-- Constant continuation credit sums over all category weights. -/
theorem weightedSum_const (ws : List ℕ) (c : ℝ≥0∞) :
    weightedSum ws (fun _ => c) = ws.sum * c := by
  induction ws with
  | nil => simp [weightedSum]
  | cons w ws IH => simp [weightedSum, IH, add_mul]

private theorem weightedSum_zero_total (ws : List ℕ) (h : ws.sum = 0)
    (F : ℕ → ℝ≥0∞) : weightedSum ws F = 0 := by
  induction ws generalizing F with
  | nil => rfl
  | cons w ws IH =>
    have hw : w = 0 ∧ ws.sum = 0 := by simpa using h
    simp [weightedSum, hw.1, IH hw.2]

/-- With zero total tail weight, every draw selects the first category. -/
theorem zero_tail_expectation (w : ℕ) (ws : List ℕ) (hw : 0 < w) (hz : ws.sum = 0)
    (F : ℕ → ℝ≥0∞) : ∫⁻ i, F i ∂law (w :: ws) = F 0 := by
  rw [lintegral_law]
  simp only [weightedSum, List.sum_cons, hz, weightedSum_zero_total ws hz,
    add_zero]
  rw [mul_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast hw.ne') (by simp)]

/-- Separate the first category from the normalized tail categorical law. -/
theorem split_expectation (w : ℕ) (ws : List ℕ) (ht : 0 < ws.sum)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, F i ∂law (w :: ws) =
      RealCoin.pmf (Urn.bias w ws.sum) true * F 0 +
        RealCoin.pmf (Urn.bias w ws.sum) false * (∫⁻ j, F (j + 1) ∂law ws) := by
  have htotal : 0 < w + ws.sum := by omega
  have ht' : (ws.sum : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht.ne'
  rw [lintegral_law, lintegral_law, Urn.pmf_true w ws.sum htotal,
    Urn.pmf_false w ws.sum htotal]
  simp only [weightedSum, List.sum_cons, Nat.cast_add]
  rw [mul_comm ((ws.sum : ℝ≥0∞) / ((w : ℝ≥0∞) + ws.sum)),
    ENNReal.div_mul_div_cancel ht' (ENNReal.natCast_ne_top ws.sum), ENNReal.add_div]
  congr 1
  simp only [div_eq_mul_inv]
  ring

end SampLib.WeightedChoice

namespace SampLib.Multinomial

noncomputable section

/-- Every count vector has one coordinate for each category, including zero weights. -/
theorem length_ae (n : ℕ) (ws : List ℕ) : ∀ᵐ cs ∂law n ws, cs.length = ws.length := by
  by_cases h : n = 0 ∨ 0 < ws.sum
  · apply ae_iff_of_countable.mpr
    intro cs hc
    by_contra hl
    apply hc
    rw [law_singleton n ws cs h]
    have hb : ¬(cs.length = ws.length ∧ cs.sum = n) := fun hs => hl hs.1
    rw [pmf, ite_eq_right hb]
    rfl
  · simp [law, h]

private theorem binomial_step (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂Binomial.law p (n + 1) =
      RealCoin.pmf p true * (∫⁻ k, F (k + 1) ∂Binomial.law p n) +
        RealCoin.pmf p false * (∫⁻ k, F k ∂Binomial.law p n) := by
  rw [← Binomial.expectation, RealCoin.lintegral_law]
  simp [Binomial.continuation, RealCoin.credit]

private theorem full_expectation (n w : ℕ) (ws : List ℕ) (hw : 0 < w) (hz : ws.sum = 0)
    (F : List ℕ → ℝ≥0∞) :
    ∫⁻ cs, F cs ∂law n (w :: ws) = F (n :: List.replicate ws.length 0) := by
  have hb : Urn.bias w ws.sum = 1 := by
    apply Subtype.ext
    have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw.ne'
    simp [Urn.bias, hz, hw, RationalCoin.bias, hw']
  rw [← expectation n w ws F, hb, Binomial.law_one]
  simp

/-- A fresh categorical trial increments one coordinate of the existing count vector. -/
theorem trial_expectation (n : ℕ) (ws : List ℕ) (ht : 0 < ws.sum)
    (F : List ℕ → ℝ≥0∞) :
    ∫⁻ j, ∫⁻ cs, F (cs.modify j Nat.succ) ∂law n ws ∂WeightedChoice.law ws =
      ∫⁻ cs, F cs ∂law (n + 1) ws := by
  induction ws generalizing n F with
  | nil => simp at ht
  | cons w ws IH =>
    by_cases ht' : 0 < ws.sum
    · have hhead : (∫⁻ cs, F (cs.modify 0 Nat.succ) ∂law n (w :: ws)) =
          ∫⁻ k, ∫⁻ cs, F ((k + 1) :: cs) ∂law (n - k) ws
            ∂Binomial.law (Urn.bias w ws.sum) n :=
        (expectation n w ws (fun cs => F (cs.modify 0 Nat.succ))).symm
      have htail : (∫⁻ j, ∫⁻ cs, F (cs.modify (j + 1) Nat.succ) ∂law n (w :: ws)
          ∂WeightedChoice.law ws) =
          ∫⁻ k, ∫⁻ cs, F (k :: cs) ∂law (n - k + 1) ws
            ∂Binomial.law (Urn.bias w ws.sum) n := by
        calc
          _ = ∫⁻ j, ∫⁻ k, ∫⁻ cs, F (k :: cs.modify j Nat.succ) ∂law (n - k) ws
              ∂Binomial.law (Urn.bias w ws.sum) n ∂WeightedChoice.law ws := by
            apply lintegral_congr
            intro j
            exact (expectation n w ws (fun cs => F (cs.modify (j + 1) Nat.succ))).symm
          _ = ∫⁻ k, ∫⁻ j, ∫⁻ cs, F (k :: cs.modify j Nat.succ) ∂law (n - k) ws
              ∂WeightedChoice.law ws ∂Binomial.law (Urn.bias w ws.sum) n :=
            lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
          _ = _ := lintegral_congr fun k => IH (n - k) ht' (fun cs => F (k :: cs))
      have hrest :
          (∫⁻ k, ∫⁻ cs, F (k :: cs) ∂law (n + 1 - k) ws
            ∂Binomial.law (Urn.bias w ws.sum) n) =
          ∫⁻ k, ∫⁻ cs, F (k :: cs) ∂law (n - k + 1) ws
            ∂Binomial.law (Urn.bias w ws.sum) n := by
        apply lintegral_congr_ae
        filter_upwards [Binomial.support (Urn.bias w ws.sum) n] with k hk
        congr 2
        omega
      rw [WeightedChoice.split_expectation w ws ht', hhead, htail,
        ← expectation (n + 1) w ws F, binomial_step]
      simpa only [Nat.add_sub_add_right] using congrArg
        (fun x => (RealCoin.pmf (Urn.bias w ws.sum) true *
          (∫⁻ k, ∫⁻ cs, F ((k + 1) :: cs) ∂law (n - k) ws
            ∂Binomial.law (Urn.bias w ws.sum) n)) +
          RealCoin.pmf (Urn.bias w ws.sum) false * x) hrest.symm
    · have hz : ws.sum = 0 := by omega
      have hw : 0 < w := by simpa [List.sum_cons, hz] using ht
      rw [WeightedChoice.zero_tail_expectation w ws hw hz,
        full_expectation n w ws hw hz, full_expectation (n + 1) w ws hw hz]
      rfl

end

end SampLib.Multinomial
