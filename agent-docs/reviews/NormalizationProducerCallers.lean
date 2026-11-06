import SampLib.LatentNormalizationConstructor

open ProbLang
open scoped ENNReal

namespace SampLib.NormalizationProducerCallers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS LatentReal

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω] {n : ℕ}
local bi (IProp GF)

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF)
    (a d : Val rT) (s : S) (R : IProp GF) :
    iprop(R ∗ withInvariant (RepresentedReciprocalView.Nonzero D) P s) ⊢
      tglWp E pl(&Occil.PSRN.divideCoordinates &(vectorVal (fun _ : Fin 1 => a)).fst &d.fst)
        (fun v => iprop(R ∗ ViewOwns
          (vectorVal (DivideCoordinates.values (fun _ : Fin 1 => a) d))
          (withInvariant (RepresentedReciprocalView.Nonzero D) P) v s)) := by
  iintro ⟨HR, Hstate⟩
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply DivideCoordinates.twp_constructor E D P (fun _ : Fin 1 => a) d s $$ Hstate
  iintro %v Hstate
  iframe HR Hstate

example (E : CoPset) (D : Model Ω S) (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i))
    (P : (Fin n → Val rT) → S → IProp GF)
    (hc : ∀ original i, IsRepresentedViewSpec E (views i) (Rs i) (P original) (original i))
    (out : Fin n → Val rT) (i : Fin n) (s : S) (k : ℕ) :
    ⊢ Normalization.owns D views hviews P out s -∗ ↯ ∞ -∗
      (∀ t I, ⌜(Normalization.coordinate D views hviews Rs i).refines s t ∧
          (Normalization.coordinate D views hviews Rs i).Encloses t k I ∧
          (Normalization.representation D views hviews Rs i).Observed t k I⌝ -∗
        Normalization.owns D views hviews P out t -∗ ↯ ∞ -∗
        emp) -∗ tglWp E pl(&(out i).fst #int (k : ℤ)) (fun _ => emp) := by
  simpa using (Normalization.coordinateSpec E D views hviews Rs P hc out i).wp s k
    (fun _ => ∞) measurable_const (fun _ => emp)

#print axioms LatentReal.DivideCoordinates.twp_constructor
#print axioms LatentReal.Normalization.value_eq
#print axioms LatentReal.Normalization.law_eq_dirichlet
#print axioms LatentReal.Normalization.coordinateSpec
#print axioms LatentReal.Normalization.twp_constructor

end

end SampLib.NormalizationProducerCallers
