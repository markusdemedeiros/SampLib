import SampLib.PSRN.Support.LatentCoordinateSum
import SampLib.PSRN.Laws.PSRNDirichletTransport

open ProbLang
open scoped ENNReal

namespace CoordinateSumCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF) (handle : Val rT)
    (h : IsViewSpec E D P handle) :
    IsViewSpec E (CoordinateSum.model D (fun _ : Fin 2 => D) (fun _ => .refl D)) P
      (CoordinateSum.value (fun _ : Fin 2 => handle)) :=
  CoordinateSum.oracleSpec E D _ _ _ P (fun _ => h)

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF) :
    IsViewSpec E (CoordinateSum.model D (fun i : Fin 0 => i.elim0) (fun i => i.elim0)) P
      (CoordinateSum.value (fun i : Fin 0 => i.elim0) : Val rT) :=
  CoordinateSum.oracleSpec E D _ _ _ P (fun i => i.elim0)

example (E : CoPset) (handles : Fin 3 → Val rT) (P : S → IProp GF) (s : S) :
    P s ⊢ tglWp E pl(&CoordinateSum.source &(vectorVal handles).fst)
      (fun v => ViewOwns (CoordinateSum.value handles) P v s) :=
  CoordinateSum.twp_sum E handles P s

example (D : Model Ω S) (x : Ω) :
    (CoordinateSum.model D (fun _ : Fin 2 => D) (fun _ => .refl D)).value x =
      D.value x + D.value x := by
  rw [CoordinateSum.value_eq]
  simp
  ring

#print axioms CoordinateSum.twp_sum
#print axioms CoordinateSum.oracleSpec
#print axioms CoordinateSum.value_eq
#print axioms CoordinateSum.measurableError
#print axioms SampLib.PSRNDirichletLaw.law_eq_of_proposal
#print axioms SampLib.PSRNDirichletLaw.expectation_of_proposal

end

end CoordinateSumCallers
