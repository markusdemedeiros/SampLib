import SampLib.Samplers.LogOnePlusFactory
import SampLib.Samplers.Complement
import Samplers.Bernoulli.Elementary

/-! # Complement of the lazy-uniform logarithmic factory -/

open ProbLang
open scoped ENNReal

namespace SampLib.ComplementLogOnePlus

noncomputable section

abbrev bias (p : unitInterval) := unitInterval.symm (LogOnePlusFactory.bias p)

theorem bias_coe (p : unitInterval) : (bias p : ℝ) = 1 - Real.log (1 + (p : ℝ)) := rfl

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

private theorem factory_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.logOnePlusFactory = Occil.logOnePlusFactory :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem factory_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.logOnePlusFactory : Exp rT) = Occil.logOnePlusFactory :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.logOnePlusFactory, Occil.oneDivOnePlus, Occil.sampleGeometricBag,
      Occil.uniformBagStep, Occil.newUniformBag, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Negate the verified logarithmic result, for every input bias including both endpoints. -/
theorem twp_complementLogOnePlus (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p)) -∗
      tglWp E pl(&Occil.FactoryExtra.complementLogOnePlus &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 2 twp_pure
  isimp only [factory_open, factory_close]
  twp_bind pl(&Occil.logOnePlusFactory &coin.fst #())
  isimp only [← Complement.expectation_preservation (LogOnePlusFactory.bias p) F] at Hcredit
  iapply ((LogOnePlusFactory.logOnePlusFactory_distSpec E p coin hcoin).wp
    (fun b => F (!b)) (measurable_of_finite _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  twp_value
  imodintro
  iexists !b
  iframe Hcredit
  ipureintro
  simp only [Val.ext_iff, bool_not]

/-- The output bias is exactly 1-log(1+p). -/
theorem complementLogOnePlus_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementLogOnePlus &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := wand_entails (twp_complementLogOnePlus E p coin hcoin F)

end specification

end

end SampLib.ComplementLogOnePlus
