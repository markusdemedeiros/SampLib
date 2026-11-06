import SampLib.LatentConstantView
import SampLib.LatentWorldRelations
import SampLib.LatentArithmeticMeasuredError

/-! # The common sum of a vector of shared latent views -/

namespace SampLib.LatentReal.CoordinateSum

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

private def projection (D : Model Ω S) : (n : ℕ) → (views : Fin n → Model Ω S) →
    (∀ i, D.SameWorld (views i)) → {N : Model Ω S // D.SameWorld N}
  | 0, _, _ => ⟨D.constant 0, D.sameWorld_constant 0⟩
  | n + 1, views, hviews =>
    let tail := projection D n (Fin.tail views) (fun i => hviews i.succ)
    let hsum := (hviews 0).between tail.property
    ⟨(views 0).add tail.val hsum, (hviews 0).trans hsum.add_left⟩

/-- Adding coordinates retains the one posterior and physical refinement relation. -/
def model (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : Model Ω S := (projection D n views hviews).val

theorem sameWorld (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : D.SameWorld (model D views hviews) :=
  (projection D n views hviews).property

/-- All terms refer to coordinates of the same latent sample. -/
theorem value_eq (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (x : Ω) :
    (model D views hviews).value x = ∑ i, (views i).value x := by
  induction n with
  | zero => simp [model, projection, Model.constant]
  | succ n ih =>
    simp only [model, projection, Model.add, Fin.sum_univ_succ]
    exact congrArg ((views 0).value x + ·)
      (by simpa only [model, Fin.tail] using ih (Fin.tail views) (fun i => hviews i.succ))

theorem measurableError (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (herror : ∀ i, (views i).MeasurableError) :
    (model D views hviews).MeasurableError := by
  induction n with
  | zero => exact fun _ => measurable_const
  | succ n ih =>
    exact (herror 0).add
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => herror i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ)))

end

end SampLib.LatentReal.CoordinateSum
