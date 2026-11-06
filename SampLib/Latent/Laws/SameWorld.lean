module

public import SampLib.Latent.Laws.Model

@[expose] public section

/-! # Models that share one latent world

Two models share a world when they have the same posteriors and refinements. Their real
projections may differ.
-/

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Two real projections may differ while sharing posteriors and physical refinements. -/
structure SameWorld (left right : Model Ω S) : Prop where
  posterior_eq : ∀ s, right.posterior s = left.posterior s
  refines_iff : ∀ s t, right.refines s t ↔ left.refines s t

namespace SameWorld

variable {left right : Model Ω S}

theorem refl (D : Model Ω S) : SameWorld D D := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

end SameWorld

end Model

end

end SampLib.LatentReal
