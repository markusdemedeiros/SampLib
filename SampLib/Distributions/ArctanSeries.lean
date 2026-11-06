module

public import SampLib.Distributions.AlternatingEnclosure
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Alternating reciprocal-arctangent enclosures and Machin's formula -/

open Filter
open scoped BigOperators Topology

namespace SampLib.ArctanSeries

noncomputable section

/-- The positive magnitudes in the Taylor series of `atan(1/q)`. -/
def coefficient (q n : ℕ) : ℝ := ((q : ℝ)⁻¹) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private theorem inverse_bounds (q : ℕ) (hq : 2 ≤ q) :
    0 < (q : ℝ)⁻¹ ∧ (q : ℝ)⁻¹ < 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  refine ⟨inv_pos.mpr hq0, ?_⟩
  simpa only [one_div] using (div_lt_iff₀ hq0).mpr (show (1 : ℝ) < 1 * q by simpa using hq1)

theorem coefficient_nonneg (q n : ℕ) : 0 ≤ coefficient q n := by
  unfold coefficient
  positivity

theorem coefficient_anti (q : ℕ) (hq : 2 ≤ q) : Antitone (coefficient q) := by
  obtain ⟨hr0, hr1⟩ := inverse_bounds q hq
  apply antitone_nat_of_succ_le
  intro n
  unfold coefficient
  exact div_le_div₀ (pow_nonneg hr0.le _)
    (pow_le_pow_of_le_one hr0.le hr1.le (by omega)) (by positivity)
    (by exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * (n + 1) + 1))

/-- A geometric majorant also bounds the absolute Taylor series. -/
theorem coefficient_le_geometric (q n : ℕ) (hq : 2 ≤ q) :
    coefficient q n ≤ ((q : ℝ)⁻¹) ^ n := by
  obtain ⟨hr0, hr1⟩ := inverse_bounds q hq
  calc
    _ ≤ ((q : ℝ)⁻¹) ^ (2 * n + 1) := div_le_self (pow_nonneg hr0.le _)
      (by exact_mod_cast (by omega : 1 ≤ 2 * n + 1))
    _ ≤ _ := pow_le_pow_of_le_one hr0.le hr1.le (by omega)

theorem coefficient_summable (q : ℕ) (hq : 2 ≤ q) : Summable (coefficient q) := by
  obtain ⟨hr0, hr1⟩ := inverse_bounds q hq
  have hgeom : Summable (fun n : ℕ => ((q : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_lt_one hr0.le hr1
  apply hgeom.of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_of_nonneg (coefficient_nonneg q n)] using
    coefficient_le_geometric q n hq

/-- The signed coefficients sum to the actual arctangent, not an abstract series oracle. -/
theorem hasSum (q : ℕ) (hq : 2 ≤ q) :
    HasSum (fun n => AlternatingEnclosure.sign n * coefficient q n)
      (Real.arctan (q : ℝ)⁻¹) := by
  obtain ⟨hr0, hr1⟩ := inverse_bounds q hq
  have h := Real.hasSum_arctan (x := (q : ℝ)⁻¹)
    (by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1)
  convert h using 1
  funext n
  simp only [AlternatingEnclosure.sign_eq, coefficient, div_eq_mul_inv, mul_assoc]

abbrev lower (q : ℕ) := AlternatingEnclosure.lower (coefficient q)

abbrev upper (q : ℕ) := AlternatingEnclosure.upper (coefficient q)

theorem enclosure (q : ℕ) (hq : 2 ≤ q) (n : ℕ) :
    lower q n ≤ Real.arctan (q : ℝ)⁻¹ ∧ Real.arctan (q : ℝ)⁻¹ ≤ upper q n := by
  have h := AlternatingEnclosure.limit_mem (coefficient q) (coefficient_anti q hq)
    (coefficient_nonneg q) (coefficient_summable q hq) n
  rwa [(hasSum q hq).tsum_eq] at h

theorem lower_mono (q : ℕ) (hq : 2 ≤ q) : Monotone (lower q) :=
  AlternatingEnclosure.lower_mono (coefficient q) (coefficient_anti q hq)

theorem upper_anti (q : ℕ) (hq : 2 ≤ q) : Antitone (upper q) :=
  AlternatingEnclosure.upper_anti (coefficient q) (coefficient_anti q hq)

theorem lower_one (q : ℕ) : lower q 1 = (q : ℝ)⁻¹ - ((q : ℝ)⁻¹) ^ 3 / 3 := by
  norm_num [lower, AlternatingEnclosure.lower, AlternatingEnclosure.partialSum,
    AlternatingEnclosure.sign, coefficient, Finset.sum_range_succ, sub_eq_add_neg]

theorem upper_one (q : ℕ) : upper q 1 = (q : ℝ)⁻¹ := by
  norm_num [upper, AlternatingEnclosure.upper, AlternatingEnclosure.partialSum,
    AlternatingEnclosure.sign, coefficient, Finset.sum_range_succ]

theorem coefficient_tendsto (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (coefficient q) atTop (𝓝 0) := (coefficient_summable q hq).tendsto_atTop_zero

/-- Machin's identity links the two convergent series to the mathematical constant π. -/
theorem machin : 16 * Real.arctan (5 : ℝ)⁻¹ - 4 * Real.arctan (239 : ℝ)⁻¹ = Real.pi := by
  linarith [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]

def piLower (n : ℕ) : ℝ := 16 * lower 5 (n + 1) - 4 * upper 239 (n + 1)

def piUpper (n : ℕ) : ℝ := 16 * upper 5 (n + 1) - 4 * lower 239 (n + 1)

theorem pi_mem (n : ℕ) : piLower n ≤ Real.pi ∧ Real.pi ≤ piUpper n := by
  have ha := enclosure 5 (by decide) (n + 1)
  have hb := enclosure 239 (by decide) (n + 1)
  have hm := machin
  constructor <;> dsimp [piLower, piUpper] <;> linarith

/-- Every source enclosure has a strictly positive lower endpoint, uniformly above three. -/
theorem pi_lower_gt_three (n : ℕ) : 3 < piLower n := by
  have ha := lower_mono 5 (by decide) (show 1 ≤ n + 1 by omega)
  have hb := upper_anti 239 (by decide) (show 1 ≤ n + 1 by omega)
  have hbase : (3 : ℝ) < 16 * lower 5 1 - 4 * upper 239 1 := by
    norm_num [lower_one, upper_one]
  dsimp [piLower]
  linarith

theorem pi_width (n : ℕ) :
    piUpper n - piLower n = 16 * coefficient 5 (n + 1) + 4 * coefficient 239 (n + 1) := by
  have ha := AlternatingEnclosure.width (coefficient 5) (n + 1)
  have hb := AlternatingEnclosure.width (coefficient 239) (n + 1)
  change upper 5 (n + 1) - lower 5 (n + 1) = _ at ha
  change upper 239 (n + 1) - lower 239 (n + 1) = _ at hb
  dsimp [piUpper, piLower]
  linarith

/-- The concrete Machin intervals shrink to zero width. -/
theorem pi_width_tendsto : Tendsto (fun n => piUpper n - piLower n) atTop (𝓝 0) := by
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop_mono Nat.le_succ tendsto_id
  have ha := ((coefficient_tendsto 5 (by decide)).comp hsucc).const_mul 16
  have hb := ((coefficient_tendsto 239 (by decide)).comp hsucc).const_mul 4
  simpa only [Function.comp_apply, mul_zero, add_zero, pi_width] using ha.add hb

end

end SampLib.ArctanSeries
