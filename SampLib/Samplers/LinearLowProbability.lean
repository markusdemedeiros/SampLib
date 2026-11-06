import SampLib.Samplers.LowProbabilityRepair

/-! # Low-probability linear Bernoulli factory

The half-margin repair makes the inner linear call valid on the full advertised
domain. The verified wrapper is definitionally the canonical sampler.
-/

open ProbLang

namespace SampLib.LinearLowProbability

noncomputable section

abbrev Admissible := LowProbabilityMargin.Admissible

def bias (p : unitInterval) (a b m n : ℤ) (h : Admissible p a b m n) : unitInterval :=
  (LowProbabilityRepair.Parameters.mk a b m n h).bias

@[simp] theorem bias_coe (p : unitInterval) (a b m n : ℤ) (h : Admissible p a b m n) :
    (bias p a b m n h : ℝ) = Gambler.ratio p a b := rfl

theorem source_eq {rT : Type} :
    (Occil.FactoryExtra.linearLowProbability : Exp rT) = LowProbabilityRepair.algorithm := rfl

section specification

open Iris TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] [ProbLangDist.IsUniformInt rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- Exact linear output bias for every valid low-probability bound. -/
theorem linearLowProbability_distSpec (E : CoPset) (p : unitInterval) (a b m n : ℤ)
    (h : Admissible p a b m n) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linearLowProbability &coin.fst #int a #int b #int m #int n #())
      (RealCoin.law (bias p a b m n h)) Val.bool := by
  rw [source_eq]
  exact LowProbabilityRepair.lowProbabilityRepair_distSpec E p ⟨a, b, m, n, h⟩ coin hcoin

end specification

end

end SampLib.LinearLowProbability
