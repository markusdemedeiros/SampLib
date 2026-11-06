import SampLib.LatentUniformAbove

/-! Full joint continuation and unrelated ownership survive the actual reversed comparison. -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.UniformAbove.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

theorem framed (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (O : Val rT → S → IProp GF) (horacle : IsOracleSpec E D O)
    (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b))
    (Q : IProp GF) :
    iprop(O source s ∗ ↯ (LatentCoin.credit D s (bias D) G) ∗ Q) ⊢
      tglWp E pl(&Occil.PSRN.less &source.fst (&Occil.PSRN.newUniform #()))
        (fun result : Val rT => iprop(∃ (b : Bool) (t : S),
          ⌜result = Val.bool b ∧ D.refines s t⌝ ∗ O source t ∗
          ↯ (∫⁻ ω, G b ω ∂D.posterior t) ∗ Q)) := by
  iintro ⟨Hstate, Hcredit, HQ⟩
  iapply (programSpec E D herror O horacle).wp source s G hG _ $$ Hstate Hcredit
  iintro %b %t %ht Hstate Hcredit
  iexists b, t
  iframe Hstate Hcredit HQ
  ipureintro
  exact ⟨rfl, ht⟩

#print axioms twp_above
#print axioms programSpec
#print axioms expectation
#print axioms framed

end

end SampLib.LatentReal.UniformAbove.ProducerCallers
