import SampLib.PSRN.Support.LatentCoordinateSum
import SampLib.PSRN.Support.LatentRepresentedDivision
import SampLib.PSRN.Laws.PSRNDirichletTransport

/-! # One normalizer for every coordinate of a represented vector -/

namespace SampLib.LatentReal.Normalization

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}

def denominator (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : Model Ω S :=
  CoordinateSum.model D views hviews

def denominatorRepresentation (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i)) :
    Representation (denominator D views hviews) :=
  CoordinateSum.representation D views hviews Rs

def coordinate (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i))
    (i : Fin n) : Model Ω S :=
  RepresentedDivision.model (views i) (denominator D views hviews)
    ((hviews i).between (CoordinateSum.sameWorld D views hviews))
    (denominatorRepresentation D views hviews Rs)

def representation (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i))
    (i : Fin n) : Representation (coordinate D views hviews Rs i) :=
  RepresentedDivision.representation (views i) (denominator D views hviews)
    ((hviews i).between (CoordinateSum.sameWorld D views hviews)) (Rs i)
    (denominatorRepresentation D views hviews Rs)

theorem sameWorld (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i)) (i : Fin n) :
    D.SameWorld (coordinate D views hviews Rs i) :=
  (hviews i).trans (RepresentedDivision.sameWorld _ _ _ _)

theorem value_eq (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i)) (x : Ω) :
    vectorValue (coordinate D views hviews Rs) x =
      PSRNDirichletLaw.normalize (vectorValue views x) := by
  funext i
  exact (RepresentedDivision.value_eq _ _ _ _ x).trans
    (congrArg ((views i).value x / ·) (CoordinateSum.value_eq D views hviews x))

theorem law_eq_dirichlet (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i)) (s : S)
    (shape : Fin n → ℝ) (hshape : ∀ i, 0 < shape i)
    (hlaw : vectorLaw D views s = PSRNDirichletLaw.proposal shape hshape) :
    vectorLaw D (coordinate D views hviews Rs) s = PSRNDirichletLaw.law shape hshape := by
  unfold vectorLaw
  rw [show vectorValue (coordinate D views hviews Rs) =
    (fun x => PSRNDirichletLaw.normalize (vectorValue views x)) from
      funext (value_eq D views hviews Rs)]
  exact PSRNDirichletLaw.law_eq_of_proposal (D.posterior s) (vectorValue views)
    (measurable_vectorValue views) shape hshape hlaw

end

end SampLib.LatentReal.Normalization
