module

public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Bernoulli law of `n` successive successes

One flip followed by `n` successes has the Bernoulli expectation with bias `p^(n+1)`.
-/

open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow)
open scoped ENNReal

namespace SampLib.IterateCoin

noncomputable section

/-- Probability that all `n` flips succeed. -/
def bias (p : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(p : ℝ) ^ n, pow_nonneg p.2.1 _, pow_le_one₀ p.2.1 p.2.2⟩

abbrev law (p : unitInterval) (n : ℕ) := RealCoin.law (bias p n)

def credit (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (bias p n) F

def continuation (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then credit p n F else F false

@[simp] theorem credit_zero (p : unitInterval) (F : Bool → ℝ≥0∞) :
    credit p 0 F = F true := by
  simp [credit, RealCoin.credit, RealCoin.pmf, bias]

/-- One flip followed by `n` successes preserves the Bernoulli(`p^(n+1)`) expectation. -/
theorem expectation (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, continuation p n F b ∂RealCoin.law p = credit p (n + 1) F := by
  have hpow : ofReal ((p : ℝ) ^ (n + 1)) =
      ofReal (p : ℝ) * ofReal ((p : ℝ) ^ n) := by
    rw [ofReal_pow p.2.1, ofReal_pow p.2.1, pow_succ]
    ring
  have hfalse : ofReal (p : ℝ) * ofReal (1 - (p : ℝ) ^ n) +
      ofReal (1 - (p : ℝ)) = ofReal (1 - (p : ℝ) ^ (n + 1)) := by
    rw [← ofReal_mul p.2.1,
      ← ofReal_add (mul_nonneg p.2.1 (sub_nonneg.mpr (pow_le_one₀ p.2.1 p.2.2)))
        (sub_nonneg.mpr p.2.2)]
    congr 1
    ring
  rw [RealCoin.lintegral_law]
  simp only [RealCoin.credit, RealCoin.pmf, continuation, credit, bias,
    Bool.false_eq_true, ite_true, ite_false]
  rw [hpow, ← hfalse]
  ring

end

end SampLib.IterateCoin
