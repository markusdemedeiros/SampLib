module

public import SampLib.Uniform.Laws.RealCoin
public import SampLib.Common.Laws.Geometric

@[expose] public section

/-! # Geometric failure counts and their retry kernel

The count of successes before the first failure is geometric with stop bias `1-p`. A
retry with amplification `factor p` conserves the continuation and termination credit.
-/

open ENNReal (ofReal ofReal_add coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.GeometricFailures

open RealCoin (pmf lintegral_law)

noncomputable section

abbrev stopBias (p : unitInterval) := unitInterval.symm p
abbrev law (p : unitInterval) := ProbabilityTheory.geometricMeasure (stopBias p)

def credit (p : unitInterval) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ n, F n ∂law p

section termination

def factor (p : unitInterval) : ℝ≥0 := 1 + unitInterval.toNNReal (stopBias p)

theorem one_lt_factor (p : unitInterval) (hp : (p : ℝ) < 1) : 1 < factor p := by
  change 1 < 1 + unitInterval.toNNReal (stopBias p)
  apply lt_add_of_pos_right
  have hstop : 0 < (stopBias p : ℝ) := by change 0 < 1 - (p : ℝ); linarith
  exact_mod_cast hstop

end termination

def coinCredit (p : unitInterval) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : Bool → ℝ≥0∞
  | true => credit p (fun n => F (n + 1)) + factor p * ε
  | false => F 0 + pmf p false * ε

/-- The geometric recurrence and `p(2-p)+(1-p)²=1` conserve all continuation credit. -/
theorem expectation (p : unitInterval) (hp : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, coinCredit p F ε b ∂RealCoin.law p = credit p F + ε := by
  have hstop : (stopBias p : ℝ) > 0 := by change 1 - (p : ℝ) > 0; linarith
  have hne : stopBias p ≠ 0 := by intro h; simp [h] at hstop
  have hrec : credit p F = pmf p false * F 0 +
      pmf p true * credit p (fun n => F (n + 1)) := by
    simpa [credit, law, stopBias, pmf, unitInterval.coe_symm_eq] using
      ProbabilityTheory.lintegral_geometricMeasure_succ (stopBias p) hne F
  have hk : (factor p : ℝ≥0∞) = 1 + pmf p false := by
    simp [factor, coe_nnreal_eq, pmf, stopBias, unitInterval.coe_symm_eq]
    rw [ofReal_add zero_le_one (sub_nonneg.mpr p.2.2), ENNReal.ofReal_one]
  have hterm : pmf p true * factor p + pmf p false * pmf p false = 1 := by
    calc
      _ = (pmf p true + pmf p false) * pmf p false + pmf p true := by rw [hk]; ring
      _ = _ := by rw [RealCoin.pmf_sum, one_mul, add_comm, RealCoin.pmf_sum]
  rw [lintegral_law]
  calc
    _ = (pmf p false * F 0 + pmf p true * credit p (fun n => F (n + 1))) +
        (pmf p true * factor p + pmf p false * pmf p false) * ε := by
      simp [RealCoin.credit, coinCredit]
      ring
    _ = _ := by rw [← hrec, hterm, one_mul]

end

end SampLib.GeometricFailures
