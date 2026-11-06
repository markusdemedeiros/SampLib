import SampLib.PSRN.Support.LatentConstantView
import SampLib.PSRN.Support.LatentWorldRelations

/-! # The squared norm as a projection of one shared latent vector -/

namespace SampLib.LatentReal.NormSquared

noncomputable section

open scoped BigOperators

variable {Ω S : Type} [MeasurableSpace Ω]

private def projection (D : Model Ω S) : (n : ℕ) → (views : Fin n → Model Ω S) →
    (∀ i, D.SameWorld (views i)) → {N : Model Ω S // D.SameWorld N}
  | 0, _, _ => ⟨D.constant 0, D.sameWorld_constant 0⟩
  | n + 1, views, hviews =>
    let tail := projection D n (Fin.tail views) (fun i => hviews i.succ)
    let square := (views 0).multiply (views 0) (.refl _)
    let hsquare : D.SameWorld square := (hviews 0).trans (.multiply_left (.refl _))
    let hsum := hsquare.between tail.property
    ⟨square.add tail.val hsum, hsquare.trans hsum.add_left⟩

/-- Squaring aliases each coordinate; adding coordinates retains their joint posterior. -/
def model (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : Model Ω S := (projection D n views hviews).val

theorem sameWorld (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : D.SameWorld (model D views hviews) :=
  (projection D n views hviews).property

/-- This is the joint squared norm, without assumptions of coordinate independence. -/
theorem value_eq (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (x : Ω) :
    (model D views hviews).value x = ∑ i, ((views i).value x) ^ 2 := by
  induction n with
  | zero => simp [model, projection, Model.constant]
  | succ n ih =>
    simp only [model, projection, Model.add, Model.multiply, Fin.sum_univ_succ, pow_two]
    exact congrArg ((views 0).value x * (views 0).value x + ·)
      (by simpa only [model, Fin.tail, pow_two] using
        ih (Fin.tail views) (fun i => hviews i.succ))

end

end SampLib.LatentReal.NormSquared
