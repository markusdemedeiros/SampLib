import SampLib.PSRN.Support.LatentAddition
import SampLib.PSRN.Support.LatentMultiplication
import SampLib.Latent.LatentViews
import SampLib.Latent.Laws.MeasuredError
import SampLib.PSRN.Support.LatentRationalTranslate
import SampLib.PSRN.Support.LatentRationalScale

/-! # Shared worlds and measurable errors of arithmetic views

Sums, products, and rational maps of views on one world stay on that world. Their
observation errors stay measurable.
-/

namespace SampLib.LatentReal.Model.SameWorld

variable {Ω S : Type} [MeasurableSpace Ω] {left middle right : Model Ω S}

theorem symm (h : left.SameWorld right) : right.SameWorld left where
  posterior_eq s := (h.posterior_eq s).symm
  refines_iff s t := (h.refines_iff s t).symm

theorem trans (h₁ : left.SameWorld middle) (h₂ : middle.SameWorld right) :
    left.SameWorld right where
  posterior_eq s := (h₂.posterior_eq s).trans (h₁.posterior_eq s)
  refines_iff s t := (h₂.refines_iff s t).trans (h₁.refines_iff s t)

/-- Two projections can be related through their common underlying world. -/
theorem between (h₁ : middle.SameWorld left) (h₂ : middle.SameWorld right) :
    left.SameWorld right := h₁.symm.trans h₂

theorem add_left (h : left.SameWorld right) : left.SameWorld (left.add right h) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

theorem multiply_left (h : left.SameWorld right) : left.SameWorld (left.multiply right h) :=
  ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

end SampLib.LatentReal.Model.SameWorld

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
