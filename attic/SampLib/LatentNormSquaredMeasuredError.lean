import SampLib.LatentNormSquaredModel
import SampLib.PSRN.Support.LatentArithmeticMeasuredError

/-! # Measurable uncertainty of squared-norm observations -/

namespace SampLib.LatentReal.NormSquared

variable {Ω S : Type} [MeasurableSpace Ω]

theorem measurableError (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (herror : ∀ i, (views i).MeasurableError) :
    (model D views hviews).MeasurableError := by
  induction n with
  | zero => exact fun _ => measurable_const
  | succ n ih =>
    exact ((herror 0).multiply (herror 0) (.refl _)).add
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => herror i.succ))
      (((hviews 0).trans (.multiply_left (.refl _))).between
        (sameWorld D (Fin.tail views) (fun i => hviews i.succ)))

end SampLib.LatentReal.NormSquared
