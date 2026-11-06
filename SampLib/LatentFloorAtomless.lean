import SampLib.Distributions.LatentReal.FloorKernel

/-! # Integer-grid avoidance from an atomless observable law -/

open MeasureTheory

namespace SampLib.LatentReal.Floor

variable {Ω S : Type} [MeasurableSpace Ω]

/-- An atomless represented real avoids every nonzero integer grid simultaneously. -/
theorem avoidsGrid_of_atomless (D : Model Ω S) (s : S) (scale : ℤ) (hscale : scale ≠ 0)
    [NullSingletonClass (D.law s)] : AvoidsGrid D scale s := by
  have hk : (scale : ℝ) ≠ 0 := by exact_mod_cast hscale
  have hz (z : ℤ) : ∀ᵐ x ∂D.posterior s, D.value x ≠ (z : ℝ) / scale :=
    ae_of_ae_map D.measurable_value.aemeasurable ((D.law s).ae_ne ((z : ℝ) / scale))
  have hall : ∀ᵐ x ∂D.posterior s, ∀ z : ℤ, D.value x ≠ (z : ℝ) / scale :=
    ae_all_iff.mpr hz
  filter_upwards [hall] with x hx
  intro heq
  exact hx (output D scale x) ((eq_div_iff hk).mpr heq)

end SampLib.LatentReal.Floor
