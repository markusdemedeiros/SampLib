import SampLib.Bernoulli.Syntax.EnvelopeFactory

open ProbLang

namespace ExactEnvelopeSourceCallers

open SampLib SampLib.FactoryFractions SampLib.EnvelopeFactory

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

example (E : CoPset) (coin bounds next : Val rT) (l : Loc)
    (n heads : ℕ) (lo hi : Fraction) (Φ : Val rT → IProp GF) (R : IProp GF) :
    iprop(tglWp E (Program.round coin bounds next l n heads lo hi) Φ ∗ R) ⊢
      tglWp E (Program.call coin bounds next l n heads lo hi)
        (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨Hwp, HR⟩
  iapply Program.twp_open_round E coin bounds next l n heads lo hi
  iapply tglWp_wand
  isplitl [Hwp]
  · iexact Hwp
  iintro %v Hpost
  iframe Hpost HR

example (E : CoPset) (coin bounds next : Val rT) (Φ : Val rT → IProp GF)
    (R : IProp GF) :
    iprop(tglWp E (Program.initialization coin bounds next) Φ ∗ R) ⊢
      tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
        &coin.fst &bounds.fst &next.fst #()) (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨Hwp, HR⟩
  iapply Program.twp_open_initialization E coin bounds next
  iapply tglWp_wand
  isplitl [Hwp]
  · iexact Hwp
  iintro %v Hpost
  iframe Hpost HR

example (E : CoPset) (coin bounds next : Val rT) (l : Loc)
    (Φ : Val rT → IProp GF) (R : IProp GF) :
    iprop(tglWp E (Program.call coin bounds next l 0 0
      (Fraction.ofRat 0) (Fraction.ofRat 1)) Φ ∗ R) ⊢
      tglWp E (.app (.lam (Program.bagBody coin bounds next)) (Val.loc l).fst)
        (fun v => iprop(Φ v ∗ R)) := by
  iintro ⟨Hwp, HR⟩
  iapply Program.twp_open_bag E coin bounds next l
  iapply tglWp_wand
  isplitl [Hwp]
  · iexact Hwp
  iintro %v Hpost
  iframe Hpost HR

#print axioms SampLib.EnvelopeFactory.Program.source_eq
#print axioms SampLib.EnvelopeFactory.Program.loop_lc
#print axioms SampLib.EnvelopeFactory.Program.twp_open_round
#print axioms SampLib.EnvelopeFactory.Program.twp_open_initialization
#print axioms SampLib.EnvelopeFactory.Program.twp_open_bag

end

end ExactEnvelopeSourceCallers
