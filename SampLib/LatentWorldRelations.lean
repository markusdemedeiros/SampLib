import SampLib.LatentAddition
import SampLib.LatentMultiplication

/-! # Changing the reference view of a shared latent world -/

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
