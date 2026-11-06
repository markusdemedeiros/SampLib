import SampLib.Uniform.Laws.RealCoin

/-! # Continuation credits for deterministic Bernoulli endpoints -/

open scoped ENNReal

namespace SampLib.RealCoin

@[simp] theorem credit_zero (F : Bool → ℝ≥0∞) : credit 0 F = F false := by
  simp [credit, pmf]

@[simp] theorem credit_one (F : Bool → ℝ≥0∞) : credit 1 F = F true := by
  simp [credit, pmf]

end SampLib.RealCoin
