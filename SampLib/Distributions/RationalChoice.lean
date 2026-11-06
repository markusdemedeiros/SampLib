import SampLib.Distributions.WeightedSums

/-! # Categorical probabilities from exact rational weights

Positive denominators admit one common integer scale. Multiplying all rational
weights by that scale preserves their normalized expectation, including infinity.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.RationalChoice

noncomputable section

def denominator (ws : List (ℕ × ℕ)) : ℕ := (ws.map Prod.snd).prod

def normalize (common : ℕ) (ws : List (ℕ × ℕ)) : List ℕ :=
  ws.map (fun p => p.1 * (common / p.2))

def numerators (ws : List (ℕ × ℕ)) : ℕ := (ws.map Prod.fst).sum

def weightedSum : List (ℕ × ℕ) → (ℕ → ℝ≥0∞) → ℝ≥0∞
  | [], _ => 0
  | (a, b) :: ws, F => (a : ℝ≥0∞) / b * F 0 + weightedSum ws (fun i => F (i + 1))

def total (ws : List (ℕ × ℕ)) : ℝ≥0∞ := weightedSum ws (fun _ => 1)

theorem denominator_pos (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2) :
    0 < denominator ws := by
  induction ws with
  | nil => simp [denominator]
  | cons p ws ih =>
    have hp := hden p (by simp)
    have ht := ih (fun q hq => hden q (by simp [hq]))
    simpa only [denominator, List.map_cons, List.prod_cons] using Nat.mul_pos hp ht

theorem denominator_dvd (ws : List (ℕ × ℕ)) (p : ℕ × ℕ) (hp : p ∈ ws) :
    p.2 ∣ denominator ws := List.dvd_prod (List.mem_map.mpr ⟨p, hp, rfl⟩)

private theorem quotient_cast (common d : ℕ) (hd : 0 < d) (hdiv : d ∣ common) :
    ((common / d : ℕ) : ℝ≥0∞) = (common : ℝ≥0∞) / d := by
  calc
    _ = (((common / d : ℕ) : ℝ≥0∞) * d) / d :=
      (ENNReal.mul_div_cancel_right (by positivity) (by finiteness)).symm
    _ = _ := by rw [← Nat.cast_mul, Nat.div_mul_cancel hdiv]

/-- Exact common-denominator scaling commutes with every weighted continuation sum. -/
theorem scale_expectation (common : ℕ) (ws : List (ℕ × ℕ))
    (hden : ∀ p ∈ ws, 0 < p.2) (hdiv : ∀ p ∈ ws, p.2 ∣ common)
    (F : ℕ → ℝ≥0∞) :
    WeightedChoice.weightedSum (normalize common ws) F = common * weightedSum ws F := by
  induction ws generalizing F with
  | nil => simp [normalize, weightedSum, WeightedChoice.weightedSum]
  | cons p ws ih =>
    have hp := hden p (by simp)
    have hd := hdiv p (by simp)
    have ht := ih (fun q hq => hden q (by simp [hq]))
      (fun q hq => hdiv q (by simp [hq])) (fun i => F (i + 1))
    cases p with
    | mk a b =>
      simp only [normalize, List.map_cons, WeightedChoice.weightedSum,
        weightedSum, Nat.cast_mul]
      dsimp [normalize] at ht
      rw [ht, quotient_cast common b hp hd]
      simp only [ENNReal.div_eq_inv_mul]
      ring

private theorem numerator_le_scaled (common : ℕ) (hc : 0 < common)
    (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hdiv : ∀ p ∈ ws, p.2 ∣ common) : numerators ws ≤ (normalize common ws).sum := by
  induction ws with
  | nil => simp [numerators, normalize]
  | cons p ws ih =>
    have hp := hden p (by simp)
    have hd := hdiv p (by simp)
    have hq := Nat.div_pos (Nat.le_of_dvd hc hd) hp
    have ht := ih (fun q hq => hden q (by simp [hq]))
      (fun q hq => hdiv q (by simp [hq]))
    simp only [numerators, normalize, List.map_cons, List.sum_cons] at *
    nlinarith

theorem normalized_sum_pos (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < numerators ws) : 0 < (normalize (denominator ws) ws).sum := by
  have h := numerator_le_scaled (denominator ws) (denominator_pos ws hden) ws hden
    (fun p hp => denominator_dvd ws p hp)
  omega

/-- A rational categorical law, represented at any common exact integer denominator. -/
def law (ws : List (ℕ × ℕ)) (_hden : ∀ p ∈ ws, 0 < p.2)
    (_hs : 0 < numerators ws) : Measure ℕ :=
  WeightedChoice.law (normalize (denominator ws) ws)

instance (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < numerators ws) : IsProbabilityMeasure (law ws hden hs) := by
  let : NeZero (normalize (denominator ws) ws).sum := ⟨(normalized_sum_pos ws hden hs).ne'⟩
  dsimp [law]
  infer_instance

/-- Normalized rational weights determine the expectation independently of integer scaling. -/
theorem lintegral_law (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < numerators ws) (F : ℕ → ℝ≥0∞) :
    ∫⁻ i, F i ∂law ws hden hs = weightedSum ws F / total ws := by
  let common := denominator ws
  have hcommon := denominator_pos ws hden
  have hdiv : ∀ p ∈ ws, p.2 ∣ common := fun p hp => denominator_dvd ws p hp
  have hsum : ((normalize common ws).sum : ℝ≥0∞) = common * total ws := by
    simpa only [WeightedChoice.weightedSum_const, mul_one, total] using
      scale_expectation common ws hden hdiv (fun _ => 1)
  rw [law, WeightedChoice.lintegral_law, scale_expectation _ ws hden hdiv, hsum]
  exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

@[simp] theorem weightedSum_zero (ws : List (ℕ × ℕ)) : weightedSum ws (fun _ => 0) = 0 := by
  induction ws with
  | nil => rfl
  | cons p ws ih => cases p; simp [weightedSum, ih]

private theorem weightedSum_singleton (ws : List (ℕ × ℕ)) (i : ℕ) :
    weightedSum ws (fun j => if j = i then 1 else 0) =
      ((ws[i]?.getD (0, 1)).1 : ℝ≥0∞) / (ws[i]?.getD (0, 1)).2 := by
  induction ws generalizing i with
  | nil => simp [weightedSum]
  | cons p ws ih =>
    cases p with
    | mk a b =>
      cases i with
      | zero => simp [weightedSum]
      | succ i => simpa [weightedSum] using ih i

/-- Each category has its input rational weight divided by the rational total. -/
theorem law_singleton (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < numerators ws) (i : ℕ) :
    law ws hden hs {i} =
      (((ws[i]?.getD (0, 1)).1 : ℝ≥0∞) / (ws[i]?.getD (0, 1)).2) / total ws := by
  rw [← lintegral_indicator_one (measurableSet_singleton i)]
  simpa [Set.indicator, weightedSum_singleton] using
    lintegral_law ws hden hs (fun j => if j = i then 1 else 0)

end

end SampLib.RationalChoice
