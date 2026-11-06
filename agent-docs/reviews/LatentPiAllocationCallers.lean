import SampLib.PSRN.Support.LatentPiAllocation
import SampLib.PSRN.Support.LatentUniformRepresentation

open ProbLang
open scoped ENNReal

namespace LatentPiAllocationCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example {Ω S : Type} [MeasurableSpace Ω] (E : CoPset) (D : Model Ω S)
    (R : Representation D) (s : S) (O : Val rT → S → IProp GF) (sample : Val rT)
    (h : IsRepresentedDistSpec E pl(&sample.fst #()) D R s O) (n : ℕ) :=
  PiModel.repeatSample_vectorSpec E D R s O sample h n

example {Ω S : Type} [MeasurableSpace Ω] (E : CoPset) (D : Model Ω S)
    (R : Representation D) (s : S) (O : Val rT → S → IProp GF) (sample : Val rT)
    (h : IsRepresentedDistSpec E pl(&sample.fst #()) D R s O) (n : ℕ)
    (Φ : Val rT → IProp GF) :=
  IsRepresentedVectorSpec.wp (PiModel.repeatSample_vectorSpec E D R s O sample h n)
    (fun _ => ∞) measurable_const Φ

private def sample : Val rT :=
  ⟨Occil.PSRN.newUniform, .lam (by is_lc), by is_lc⟩

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (n : ℕ) :=
  PiModel.repeatSample_vectorSpec E LatentUniform.model LatentUniform.representation []
    LatentUniform.owns sample (by
      simpa only [sample] using LatentUniform.newUniform_representedDistSpec (rT := rT) (GF := GF) E) n

example (E : CoPset) :=
  PiModel.repeatSample_vectorSpec E LatentUniform.model LatentUniform.representation []
    LatentUniform.owns sample (by
      simpa only [sample] using LatentUniform.newUniform_representedDistSpec (rT := rT) (GF := GF) E) 0

example (E : CoPset) :=
  PiModel.repeatSample_vectorSpec E LatentUniform.model LatentUniform.representation []
    LatentUniform.owns sample (by
      simpa only [sample] using LatentUniform.newUniform_representedDistSpec (rT := rT) (GF := GF) E) 1

#print axioms PiModel.repeatSample_payloadSpec
#print axioms PiModel.repeatSample_vectorSpec
#print axioms SampLib.FiniteProductPosterior.expectation_cons
#print axioms SampLib.FiniteProductPosterior.expectation_cons_right

end

end LatentPiAllocationCallers
