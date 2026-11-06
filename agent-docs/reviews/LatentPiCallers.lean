import SampLib.PSRN.Support.LatentPiCoordinate

open ProbLang
open scoped ENNReal

namespace LatentPiCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {n : ℕ} {Ω S : Fin n → Type} [∀ i, MeasurableSpace (Ω i)]
local bi (IProp GF)

example (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i) :
    vectorLaw (PiModel.world Ds) (PiModel.view Ds) s =
      MeasureTheory.Measure.pi (fun i => (Ds i).law (s i)) := PiModel.vectorLaw_eq_pi Ds s

example (E : CoPset) (Ds : ∀ i, Model (Ω i) (S i)) (Rs : ∀ i, Representation (Ds i))
    (O : ∀ i, Val rT → S i → IProp GF) (handles : Fin n → Val rT) (i : Fin n)
    (hspec : IsRepresentedOracleSpec E (Ds i) (Rs i) (O i)) :=
  PiModel.represented_coordinateSpec E Ds Rs O handles i hspec

example (O : ∀ i, Val rT → S i → IProp GF) (handles : Fin n → Val rT)
    (s : ∀ i, S i) (i : Fin n) :
    PiModel.owns S O handles s ⊢ iprop(O i (handles i) (s i) ∗
      ∀ t : S i, O i (handles i) t -∗ PiModel.owns S O handles (Function.update s i t)) :=
  PiModel.access S O handles s i

example (E : CoPset) (Ds : ∀ i, Model (Ω i) (S i)) (Rs : ∀ i, Representation (Ds i))
    (O : ∀ i, Val rT → S i → IProp GF) (handles : Fin n → Val rT) (i : Fin n)
    (hspec : IsRepresentedOracleSpec E (Ds i) (Rs i) (O i))
    (s : ∀ i, S i) (bits : ℕ) (Φ : Val rT → IProp GF) :=
  IsRepresentedViewSpec.wp (PiModel.represented_coordinateSpec E Ds Rs O handles i hspec)
    s bits (fun _ => ∞) measurable_const Φ

#print axioms SampLib.FiniteProductPosterior.absolutelyContinuous
#print axioms SampLib.FiniteProductPosterior.expectation_coordinate
#print axioms SampLib.FiniteProductPosterior.expectation_update
#print axioms PiModel.vectorLaw_eq_pi
#print axioms PiModel.access
#print axioms PiModel.represented_coordinateSpec

end

end LatentPiCallers
