import SampLib.Weighted.Laws.HanHoshi

/-! # Posterior certificates and unresolved boundaries for Han–Hoshi -/

open Set MeasureTheory

namespace SampLib.HanHoshi

noncomputable section

/-- Integer cross products are precisely the normalized whole-cell comparisons. -/
theorem fits_iff_bounds (ws : List ℕ) (ht : 0 < ws.sum) (i value denominator : ℕ)
    (hd : 0 < denominator) :
    Fits ws.sum value denominator (ws.take i).sum (ws.take (i + 1)).sum ↔
      RealCategoricalCDF.lower ws i ≤ (value : ℝ) / denominator ∧
        ((value : ℝ) + 1) / denominator ≤ RealCategoricalCDF.upper ws i := by
  have htR : (0 : ℝ) < ws.sum := by exact_mod_cast ht
  have hdR : (0 : ℝ) < denominator := by exact_mod_cast hd
  rw [RealCategoricalCDF.lower, RealCategoricalCDF.upper,
    div_le_div_iff₀ htR hdR, div_le_div_iff₀ hdR htR]
  unfold Fits
  norm_cast

theorem rank_bounds (p : List Bool) :
    0 ≤ UniformBag.rank p ∧ UniformBag.rank p < (2 : ℤ) ^ p.length := by
  induction p with
  | nil => norm_num [UniformBag.rank]
  | cons b p ih =>
    cases b <;> simp only [UniformBag.rank, Bool.false_eq_true, ite_false, ite_true,
      zero_mul, zero_add,
      one_mul, List.length_cons, pow_succ] <;> omega

private theorem rank_cast (p : List Bool) :
    ((UniformBag.rank p).toNat : ℝ) = (UniformBag.rank p : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (rank_bounds p).1

/-- A successful whole-cell test settles the output throughout the current posterior. -/
theorem cell_resolves (ws : List ℕ) (ht : 0 < ws.sum) (p : List Bool) (i : ℕ)
    (hi : i < ws.length)
    (hfit : Fits ws.sum (UniformBag.rank p).toNat (2 ^ p.length)
      (ws.take i).sum (ws.take (i + 1)).sum) :
    ∀ᵐ u ∂DyadicPosterior.law p,
      IncompleteInformation.quantile (RealCategoricalCDF.model ws ht) u = (i : ℤ) := by
  have hbounds := (fits_iff_bounds ws ht i _ _ (by positivity)).mp hfit
  simp only [rank_cast, Nat.cast_pow, Nat.cast_ofNat] at hbounds
  filter_upwards [DyadicPosterior.ae_mem_cell p, DyadicPosterior.ae_mem_unit p] with u hu hunit
  rw [LatentUniform.cell_eq_rank] at hu
  apply (RealCategoricalCDF.quantile_interval ws ht i hi u hunit).mpr
  exact ⟨hbounds.1.trans hu.1, hu.2.trans_le hbounds.2⟩

/-- A failed scan exposes a CDF boundary strictly inside the current cell. -/
theorem unresolved_boundary (ws : List ℕ) (ht : 0 < ws.sum) (p : List Bool)
    (hnone : scan ws.sum (UniformBag.rank p).toNat (2 ^ p.length) ws 0 = none) :
    ∃ i < ws.length,
      (UniformBag.rank p : ℝ) / 2 ^ p.length < RealCategoricalCDF.upper ws i ∧
        RealCategoricalCDF.upper ws i < ((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length := by
  let value := (UniformBag.rank p).toNat
  let denominator := 2 ^ p.length
  let u : ℝ := value / denominator
  have hd : 0 < denominator := by dsimp [denominator]; positivity
  have hv : value < denominator := by
    have h := (rank_bounds p).2
    dsimp [value, denominator]
    exact_mod_cast (show ((UniformBag.rank p).toNat : ℤ) < (2 : ℤ) ^ p.length by
      rw [Int.toNat_of_nonneg (rank_bounds p).1]
      exact h)
  have hu : u ∈ Ico 0 1 := by
    dsimp [u]
    exact ⟨by positivity, (div_lt_one (by exact_mod_cast hd)).mpr (by exact_mod_cast hv)⟩
  let q := IncompleteInformation.quantile (RealCategoricalCDF.model ws ht) u
  have hq := IncompleteInformation.quantile_range (RealCategoricalCDF.model ws ht) u
  have hq0 : 0 ≤ q := hq.1
  have hqhi : q < (ws.length : ℤ) := by
    have h := hq.2
    change q ≤ (ws.length : ℤ) - 1 at h
    omega
  let i := q.toNat
  have hi : i < ws.length := by dsimp [i]; omega
  have hqi : q = (i : ℤ) := (Int.toNat_of_nonneg hq0).symm
  have hinterval := (RealCategoricalCDF.quantile_interval ws ht i hi u hu).mp hqi
  have hbad := (scan_none ws.sum value denominator ws 0).mp hnone i hi
  simp only [zero_add] at hbad
  have hupper : RealCategoricalCDF.upper ws i < ((value : ℝ) + 1) / denominator := by
    by_contra h
    exact hbad ((fits_iff_bounds ws ht i value denominator hd).mpr
      ⟨hinterval.1, not_lt.mp h⟩)
  refine ⟨i, hi, ?_, ?_⟩
  · simpa only [u, denominator, value, rank_cast, Nat.cast_pow, Nat.cast_ofNat] using hinterval.2
  · simpa only [denominator, value, rank_cast, Nat.cast_pow, Nat.cast_ofNat] using hupper

end

end SampLib.HanHoshi
