import SampLib.LatentNormSquaredModel
import SampLib.Latent.LatentVectorSpec

/-! # The joint law of a deferred squared norm -/

namespace SampLib.LatentReal.NormSquared

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {Ω S : Type} [MeasurableSpace Ω]

theorem value_nonneg (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (x : Ω) :
    0 ≤ (model D views hviews).value x := by
  rw [value_eq]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The entire vector is pushed forward by its squared Euclidean norm. -/
theorem law_eq (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (s : S) :
    (model D views hviews).law s =
      (vectorLaw D views s).map (fun v : Fin n → ℝ => ∑ i, v i ^ 2) := by
  have hnorm : Measurable (fun v : Fin n → ℝ => ∑ i, v i ^ 2) := by fun_prop
  rw [Model.law, (sameWorld D views hviews).posterior_eq s, vectorLaw,
    Measure.map_map hnorm (measurable_vectorValue views)]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun x => value_eq D views hviews x

end

end SampLib.LatentReal.NormSquared
