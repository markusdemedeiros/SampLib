import SampLib.Uniform.UniformInt

/-! # Finite support of uniform integers -/

namespace SampLib.UniformInt

open MeasureTheory

theorem ae_lt (n : ℕ) : ∀ᵐ k ∂law n, k < n := by
  apply ae_iff_of_countable.mpr
  intro k hk
  by_contra h
  apply hk
  simp [law, h]

end SampLib.UniformInt
