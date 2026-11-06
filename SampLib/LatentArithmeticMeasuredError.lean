import SampLib.LatentMeasuredError
import SampLib.LatentRationalTranslate
import SampLib.LatentRationalScale
import SampLib.LatentAddition
import SampLib.LatentMultiplication

/-! # Measurability of arithmetic observation errors -/

namespace SampLib.LatentReal.Model.MeasurableError

variable {Ω S : Type} [MeasurableSpace Ω] {left right : Model Ω S}

theorem negate (h : left.MeasurableError) : left.negate.MeasurableError := h

theorem translate (h : left.MeasurableError) (c : ℝ) : (left.translate c).MeasurableError := h

theorem scale (h : left.MeasurableError) (c : ℝ) : (left.scale c).MeasurableError :=
  fun n => (h n).mul_const |c|

theorem add (hl : left.MeasurableError) (hr : right.MeasurableError)
    (hworld : left.SameWorld right) : (left.add right hworld).MeasurableError :=
  fun n => (hl n).add (hr n)

theorem multiply (hl : left.MeasurableError) (hr : right.MeasurableError)
    (hworld : left.SameWorld right) : (left.multiply right hworld).MeasurableError := fun n =>
  (((hl n).mul right.measurable_value.abs).add
    (left.measurable_value.abs.mul (hr n))).add ((hl n).mul (hr n)) |>.const_mul 2

end SampLib.LatentReal.Model.MeasurableError
