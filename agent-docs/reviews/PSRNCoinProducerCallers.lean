import SampLib.PSRN.Support.PSRNCoin

/-! Two fresh conditional coins preserve their joint latent continuation and a frame. -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Coin.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def twice (source : Val rT) : Exp rT :=
  let call := .app (Program.value source).fst (.lit .unit)
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) call)) call

/-- The two returned bits remain conditionally independent given the same latent value. -/
theorem repeated (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (s : S) (H : Bool × Bool → Ω → ℝ≥0∞)
    (hH : ∀ p, Measurable (H p)) (R : IProp GF) :
    let bias := fun x => LatentBernoulli.bias (D.value x)
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s bias
      (fun a x => LatentCoin.kernel bias (fun b y => H (a, b) y) x)) ∗ R) ⊢
      tglWp E (twice source)
        (fun result : Val rT => iprop(∃ (a b : Bool) (t : S),
          ⌜result = Val.pair (Val.bool a) (Val.bool b) ∧ D.refines s t⌝ ∗
          owns source t ∗ ↯ (∫⁻ x, H (a, b) x ∂D.posterior t) ∗ R)) := by
  dsimp only
  iintro ⟨Hsource, Hcredit, HR⟩
  have hspec := coin_spec E D herror owns horacle
  have hmeas a := LatentCoin.measurable_kernel
    (LatentBernoulli.measurable_bias.comp D.measurable_value) (fun b => hH (a, b))
  twp_bind pl(&(Program.value source).fst #())
  iapply hspec.wp source s
    (fun a x => LatentCoin.kernel (fun x => LatentBernoulli.bias (D.value x))
      (fun b y => H (a, b) y) x) hmeas _ $$ Hsource Hcredit
  iintro %a %t %ht Hsource Hcredit
  have hcredit_eq :
      (∫⁻ x, LatentCoin.kernel (fun x => LatentBernoulli.bias (D.value x))
        (fun b y => H (a, b) y) x ∂D.posterior t) =
      LatentCoin.credit D t (fun x => LatentBernoulli.bias (D.value x))
        (fun b y => H (a, b) y) := rfl
  isimp only [hcredit_eq] at Hcredit
  twp_pure
  twp_bind pl(&(Program.value source).fst #())
  iapply hspec.wp source t (fun b x => H (a, b) x) (fun b => hH (a, b)) _ $$ Hsource Hcredit
  iintro %b %u %hu Hsource Hcredit
  twp_pures
  twp_value
  imodintro
  iexists a, b, u
  iframe Hsource Hcredit HR
  ipureintro
  exact ⟨rfl, D.refines_trans ht hu⟩

#print axioms repeated
#print axioms twp_coin
#print axioms coin_programSpec
#print axioms coin_spec
#print axioms UniformThreshold.expectation
#print axioms UniformThreshold.ae_distinct
#print axioms Program.source_eq

end

end SampLib.LatentReal.Coin.ProducerCallers
