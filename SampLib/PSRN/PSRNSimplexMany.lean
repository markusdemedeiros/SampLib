import SampLib.PSRN.Support.Simplex.Model
import SampLib.PSRN.Support.Simplex.Source
import SampLib.PSRN.Support.Simplex.NormalizationConstructor

/-! # The actual multi-coordinate exponential simplex constructor -/

open ProbLang
open scoped ENNReal SampLib.LatentReal.CoordinateSum

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def normalizedOwns (n : ℕ) : (Fin n → Val rT) → State n → IProp GF :=
  Normalization.owns (world n) (original n) (original_sameWorld n) (originalOwns n)

/-- Independent exponentials are normalized together, without observing any coordinate. -/
theorem many_payloadSpec (E : CoPset) (n : ℕ) (hn : 2 ≤ n) :
    IsLatentPayloadSpec (GF := GF) E pl(&Occil.PSRN.newSimplex #int (n : ℤ) #())
      (world n) (initial n) (VectorOwns (normalizedOwns n)) := by
  have hzero : decide ((n : ℤ) ≤ 0) = false := by simp; omega
  have hone : ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = false :=
    beq_eq_false_iff_ne.mpr (by simp; omega)
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  iapply Program.twp_open E (n : ℤ) _
  unfold Program.openedBody
  twp_pures
  rw [hzero]
  twp_pure
  twp_pures
  rw [hone]
  twp_pure
  simp only [ClosedExp.closeRec]
  twp_bind pl(&Occil.repeatSample &(Program.sampleValue (rT := rT)).fst #int (n : ℤ))
  iapply (allocationSpec E n).wp F hF _ $$ Hcredit
  iintro %handles %s %hs Hstate Hcredit
  twp_pure
  twp_pure
  simp only [ClosedExp.openRec]
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply Normalization.twp_constructor E (world n) (original n) (original_sameWorld n)
      (originalOwns n) handles s (nonzero_of_refines n (by omega) s hs) $$ Hstate
  iintro %output Hstate
  iexists s
  isplitl []
  · ipureintro
    exact hs
  unfold normalizedOwns
  iframe Hstate Hcredit

/-- Every output coordinate observes the same normalized exponential family. -/
theorem many_vectorSpec (E : CoPset) (n : ℕ) (hn : 2 ≤ n) :
    IsRepresentedVectorSpec (GF := GF) E pl(&Occil.PSRN.newSimplex #int (n : ℤ) #())
      (world n) (normalized n) (normalizedRepresentation n) (initial n) (normalizedOwns n) where
  sameWorld i := Normalization.sameWorld _ _ _ _ i
  payload := many_payloadSpec E n hn
  coordinate handles i := Normalization.coordinateSpec E (world n) (original n)
    (original_sameWorld n) (originalRepresentation n) (originalOwns n)
    (fun original i => (allocationSpec E n).coordinate original i) handles i

end

end SampLib.PSRNSimplex
