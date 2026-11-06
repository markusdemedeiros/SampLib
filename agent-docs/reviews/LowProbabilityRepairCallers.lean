import SampLib.Samplers.LowProbabilityRepair
import SampLib.Samplers.LinearLowProbability

open ProbLang
open scoped ENNReal

namespace LowProbabilityRepairCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval)
    (σ : LowProbabilityRepair.Parameters p) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law σ.bias) ∗ R -∗
      tglWp E pl(&LowProbabilityRepair.algorithm &coin.fst
        #int σ.a #int σ.b #int σ.m #int σ.n #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((LowProbabilityRepair.lowProbabilityRepair_distSpec E p σ coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HR
  itrivial

example [ProbLangDist.IsUniformInt rT] (E : CoPset) (p : unitInterval)
    (a b m n : ℤ) (h : LinearLowProbability.Admissible p a b m n) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂RealCoin.law (LinearLowProbability.bias p a b m n h)) ∗ R -∗
      tglWp E pl(&Occil.FactoryExtra.linearLowProbability &coin.fst
        #int a #int b #int m #int n #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((LinearLowProbability.linearLowProbability_distSpec E p a b m n h coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HR
  itrivial

private def originalCounterexample : LowProbabilityRepair.Parameters
    LowProbabilityMargin.counterexampleBias :=
  ⟨2, 1, 1, 4, LowProbabilityMargin.counterexample_admissible⟩

example : (originalCounterexample.bias : ℝ) = 1 / 4 := by
  norm_num [LowProbabilityRepair.Parameters.bias_coe, originalCounterexample,
    LowProbabilityMargin.counterexampleBias, Gambler.ratio]

example : LinearFactory.Admissible LowProbabilityMargin.counterexampleBias 8 2 1 2 :=
  LowProbabilityMargin.repaired_inner_admissible _ 2 1 1 4
    LowProbabilityMargin.counterexample_admissible (by norm_num)

example : ¬ LinearFactory.Admissible LowProbabilityMargin.counterexampleBias 8 2 3 4 :=
  LowProbabilityMargin.counterexample_inner_not_admissible

private def zeroParameters : LowProbabilityRepair.Parameters 0 :=
  ⟨2, 1, 0, 1, by norm_num [LowProbabilityMargin.Admissible, Gambler.ratio]⟩

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞) ∂RealCoin.law zeroParameters.bias) = 0 := by
  rw [zeroParameters.bias_zero rfl]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

end

end LowProbabilityRepairCallers

#print axioms SampLib.LowProbabilityMargin.counterexample_inner_not_admissible
#print axioms SampLib.LowProbabilityMargin.repaired_inner_admissible
#print axioms SampLib.LowProbabilityRepair.expectation
#print axioms SampLib.LowProbabilityRepair.twp_lowProbabilityRepair
#print axioms SampLib.LowProbabilityRepair.lowProbabilityRepair_distSpec
#print axioms SampLib.LinearLowProbability.source_eq
#print axioms SampLib.LinearLowProbability.linearLowProbability_distSpec
