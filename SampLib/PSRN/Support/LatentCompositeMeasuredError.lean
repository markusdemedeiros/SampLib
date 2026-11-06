import SampLib.Latent.LatentMeasuredError
import SampLib.PSRN.Support.LatentProductModel
import SampLib.PSRN.Support.LatentMixtureModel

/-! # Measurable error envelopes for product and mixture worlds -/

namespace SampLib.LatentReal.Model.MeasurableError

variable {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  {L : Model Ω₁ S₁} {R : Model Ω₂ S₂}

/-- Lifting the first component preserves measurable observation error. -/
theorem product_left (hL : L.MeasurableError) : (ProductModel.left L R).MeasurableError :=
  fun n => (hL n).comp measurable_fst

/-- The second component is measurable in the same full product world. -/
theorem product_right (hR : R.MeasurableError) : (ProductModel.right L R).MeasurableError :=
  fun n => (hR n).comp measurable_snd

/-- Selection retains the chosen component's measurable error envelope. -/
theorem mixture (hL : L.MeasurableError) (hR : R.MeasurableError)
    (p : unitInterval) (i : S₁) (j : S₂) :
    (MixtureModel.model p L R i j).MeasurableError := fun n => (hL n).sumElim (hR n)

end SampLib.LatentReal.Model.MeasurableError
