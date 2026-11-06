import SampLib.Distributions.LinearFactory

/-! # The margin in the low-probability linear factory

The outer bound `μ ≤ ρ < 1/2` gives an inner bias at most `1/2`.
The original source supplied the stronger, unjustified bound `μ / (2ρ) ≤ ρ`.
-/

namespace SampLib.LowProbabilityMargin

open ProbLang

noncomputable section

/-- The advertised domain of the low-probability wrapper. -/
def Admissible (p : unitInterval) (a b m n : ℤ) : Prop :=
  0 ≤ a ∧ 0 < b ∧ 0 ≤ m ∧ 2 * m < n ∧ Gambler.ratio p a b ≤ (m : ℝ) / n

/-- The supplied inner margin is justified only on this smaller domain. -/
theorem inner_bound_iff (μ ρ : ℝ) (hρ : 0 < ρ) :
    μ / (2 * ρ) ≤ ρ ↔ μ ≤ 2 * ρ ^ 2 := by
  rw [div_le_iff₀ (by positivity : 0 < 2 * ρ)]
  ring_nf

/-- At the advertised upper bound, a half-margin suffices for the inner call. -/
theorem half_margin (μ ρ : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ ρ) :
    μ / (2 * ρ) ≤ 1 - (1 : ℝ) / 2 := by
  rw [div_le_iff₀ (by positivity : 0 < 2 * ρ)]
  linarith

/-- `Linear(a*n,b*2*m,1,2)` meets the verified linear factory's full domain. -/
theorem repaired_inner_admissible (p : unitInterval) (a b m n : ℤ)
    (h : Admissible p a b m n) (hm : 0 < m) :
    LinearFactory.Admissible p (a * n) (b * 2 * m) 1 2 := by
  obtain ⟨ha, hb, _, hmn, hμ⟩ := h
  have hn : 0 < n := by omega
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : 0 < (m : ℝ) / n := div_pos (by exact_mod_cast hm) (by exact_mod_cast hn)
  refine ⟨mul_nonneg ha hn.le, mul_pos (mul_pos hb (by norm_num)) hm, fun _ => ?_⟩
  refine ⟨by norm_num, by norm_num, ?_⟩
  have heq : Gambler.ratio p (a * n) (b * 2 * m) =
      Gambler.ratio p a b / (2 * ((m : ℝ) / n)) := by
    simp only [Gambler.ratio, Int.cast_mul, Int.cast_ofNat]
    field_simp [hb', hm', hn']
  rw [heq]
  simpa only [Int.cast_one, Int.cast_ofNat] using half_margin _ _ hr hμ

/-- The advertised output bias is below one half, hence in the linear domain. -/
theorem outer_admissible (p : unitInterval) (a b m n : ℤ)
    (h : Admissible p a b m n) : LinearFactory.Admissible p a b 1 2 := by
  obtain ⟨ha, hb, hm, hmn, hμ⟩ := h
  refine ⟨ha, hb, fun _ => ⟨by norm_num, by norm_num, ?_⟩⟩
  have hn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : (m : ℝ) / n < 1 / 2 := by
    apply (div_lt_iff₀ hn).mpr
    have hmn' : 2 * (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  norm_num at hr ⊢
  exact hμ.trans hr.le

/-- A guard-valid input in the advertised domain. -/
def counterexampleBias : unitInterval := ⟨1 / 8, by norm_num, by norm_num⟩

theorem counterexample_admissible : Admissible counterexampleBias 2 1 1 4 := by
  norm_num [Admissible, counterexampleBias, Gambler.ratio]

/-- The actual inner call at that input violates the linear factory's margin. -/
theorem counterexample_inner_not_admissible :
    ¬ LinearFactory.Admissible counterexampleBias 8 2 3 4 := by
  norm_num [LinearFactory.Admissible, counterexampleBias, Gambler.ratio]

end

end SampLib.LowProbabilityMargin
