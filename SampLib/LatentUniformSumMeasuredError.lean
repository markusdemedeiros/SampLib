import SampLib.Samplers.PSRNUniformSum
import SampLib.LatentArithmeticMeasuredError
import SampLib.LatentCompositeMeasuredError

/-! # Measurable uncertainty for deferred uniform sums -/

namespace SampLib.PSRNUniformSum

open LatentReal

theorem measurableError (n : ℕ) : (model n).MeasurableError := by
  induction n with
  | zero => exact fun _ => measurable_const
  | succ n ih =>
    have hu : LatentUniform.model.MeasurableError := fun _ => measurable_const
    exact (Model.MeasurableError.product_left hu).add
      (Model.MeasurableError.product_right ih)
      (ProductModel.sameWorld LatentUniform.model (model n))

end SampLib.PSRNUniformSum
