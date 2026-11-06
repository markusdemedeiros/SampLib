import SampLib.PSRNSimplexModel
import SampLib.Syntax.PSRNSimplex

/-! # Independent concrete exponential allocation for simplex coordinates -/

open ProbLang

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def originalOwns (n : ℕ) : (Fin n → Val rT) → State n → IProp GF :=
  PiModel.owns (fun _ => ComponentState) (fun _ => PSRNExponential.rationalOwns 1 1)

/-- The actual callback forwards the concrete represented unit-rate exponential law. -/
theorem sampleSpec (E : CoPset) :
    IsRepresentedDistSpec (GF := GF) E pl(&(Program.sampleValue (rT := rT)).fst #())
      component componentRepresentation (LatentExponential.initial rate)
      (PSRNExponential.rationalOwns 1 1) where
  toIsLatentPayloadSpec := by
    refine ⟨fun F hF => ?_⟩
    have hbase : IsRepresentedDistSpec (GF := GF) E
        pl(&Occil.PSRN.newExponential #1 #1 #()) component componentRepresentation
        (LatentExponential.initial rate) (PSRNExponential.rationalOwns 1 1) :=
      PSRNExponential.newExponential_representedDistSpec E 1 1 (by decide) (by decide)
    iintro Hcredit
    rw [Program.sample_fst]
    twp_pure
    rw [Program.exponential_openRec]
    iapply hbase.spec F hF $$ Hcredit
  oracle := (PSRNExponential.newExponential_representedDistSpec E 1 1
    (by decide) (by decide)).oracle

/-- All constructor calls allocate one independent joint family, with exact interval protocols. -/
theorem allocationSpec (E : CoPset) (n : ℕ) :
    IsRepresentedVectorSpec (GF := GF) E
      pl(&Occil.repeatSample &(Program.sampleValue (rT := rT)).fst #int (n : ℤ))
      (world n) (original n) (originalRepresentation n) (initial n) (originalOwns n) :=
  PiModel.repeatSample_vectorSpec E component componentRepresentation
    (LatentExponential.initial rate) (PSRNExponential.rationalOwns 1 1)
    Program.sampleValue (sampleSpec E) n

end

end SampLib.PSRNSimplex
