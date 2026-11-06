import SampLib.EnvelopeRescaleStep

open ProbLang

namespace EnvelopeRescaleStepAuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib
open EnvelopeFactory FactoryFractions

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (self : Val rT) (l : Loc) (degree heads : ℕ)
    (lo hi lower upper oldLower oldUpper : Fraction)
    (hwidth : 0 < oldUpper.value - oldLower.value) (Φ : Val rT → IProp GF)
    (R : IProp GF) :
    iprop(tglWp E (Program.afterRescale self l degree heads
      (rescaledLower lo hi lower oldLower oldUpper)
      (rescaledUpper lo hi upper oldLower oldUpper)) Φ ∗ R) ⊢
      tglWp E (Program.afterConditional self l degree heads
        lo hi lower upper oldLower oldUpper) (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨Hrun, HR⟩
  iapply twp_rescale E self l degree heads lo hi lower upper oldLower oldUpper hwidth
  iapply tglWp_wand
  isplitl [Hrun]
  · iexact Hrun
  iintro %v HΦ
  iframe HΦ HR

example : 0 < (Fraction.ofRat 2).value - (Fraction.ofRat (-1)).value := by norm_num

example : (rescaledLower (.ofRat (3 / 4)) (.ofRat (-1 / 4)) (.ofRat (-2))
    (.ofRat (-1)) (.ofRat 2)).value = 13 / 12 := by
  norm_num [rescaledLower]

example : (rescaledUpper (.ofRat (3 / 4)) (.ofRat (-1 / 4)) (.ofRat 4)
    (.ofRat (-1)) (.ofRat 2)).value = -11 / 12 := by
  norm_num [rescaledUpper]

end

end EnvelopeRescaleStepAuthorCallers

#print axioms SampLib.EnvelopeFactory.twp_rescale
