import SampLib.LatentCoordinateSum
import SampLib.LatentRepresentedAddition

/-! # The common sum retains each coordinate's deterministic representation -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.CoordinateSum

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The represented denominator is the finite sum at the same requested precision. -/
def representation (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i)) :
    Representation (model D views hviews) := by
  induction n with
  | zero => exact Representation.point D 0 0 1 (by decide) (by norm_num)
  | succ n ih =>
    exact Representation.add (views 0) (model D (Fin.tail views) (fun i => hviews i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ))) (Rs 0)
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => Rs i.succ))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Repeated or aliased coordinates still consume one shared physical ownership. -/
theorem represented_oracleSpec (E : CoPset) (D : Model Ω S) {n : ℕ}
    (views : Fin n → Model Ω S) (hviews : ∀ i, D.SameWorld (views i))
    (Rs : ∀ i, Representation (views i)) (handles : Fin n → Val rT) (P : S → IProp GF)
    (hspec : ∀ i, IsRepresentedViewSpec E (views i) (Rs i) P (handles i)) :
    IsRepresentedViewSpec E (model D views hviews) (representation D views hviews Rs)
      P (value handles) := by
  induction n with
  | zero =>
    exact represented_point_viewSpec E D P 0 0 1 (by decide) (by norm_num)
  | succ n ih =>
    exact represented_add_oracleSpec E (views 0)
      (model D (Fin.tail views) (fun i => hviews i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ))) (Rs 0)
      (representation D (Fin.tail views) (fun i => hviews i.succ) (fun i => Rs i.succ)) P
      (handles 0) (value (Fin.tail handles)) (hspec 0)
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => Rs i.succ)
        (Fin.tail handles) (fun i => hspec i.succ))

end specification

end

end SampLib.LatentReal.CoordinateSum
