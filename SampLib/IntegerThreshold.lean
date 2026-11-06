import SampLib.Samplers.UniformInt
import SampLib.Samplers.RationalCoin

/-! # Bernoulli thresholds on a uniform integer rank -/

open ProbLang
open scoped ENNReal

namespace SampLib.IntegerThreshold

noncomputable section

/-- The fraction of ranks below the threshold. -/
abbrev bias (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) : unitInterval :=
  RationalCoin.bias a b (by positivity) (by exact_mod_cast hb) (by exact_mod_cast hab)

/-- Counting the accepted ranks gives the rational Bernoulli expectation. -/
theorem expectation (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (F : Bool → ℝ≥0∞) :
    (∑ k ∈ Finset.range b, RationalCoin.rankCredit a F k) / b =
      RealCoin.credit (bias a b hb hab) F := by
  simpa using RationalCoin.expectation (a : ℤ) (b : ℤ) (by positivity)
    (by exact_mod_cast hb) (by exact_mod_cast hab) F

private theorem rankCredit_eq (a : ℕ) (F : Bool → ℝ≥0∞) (k : ℕ) :
    RationalCoin.rankCredit a F k = F (decide ((k : ℤ) < (a : ℤ))) := by
  by_cases h : (k : ℤ) < (a : ℤ) <;> simp [RationalCoin.rankCredit, h]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The comparison samples even at deterministic endpoint thresholds. -/
theorem twp_threshold (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b hb hab) F) -∗
      tglWp E pl(&Occil.uniformInt #int (b : ℤ) < #int (a : ℤ))
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  twp_bind pl(&Occil.uniformInt #int (b : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply UniformInt.twp_uniformInt E b hb (RationalCoin.rankCredit a F)
    rw [expectation a b hb hab F]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_pures
  twp_value
  imodintro
  iexists decide ((k : ℤ) < (a : ℤ))
  isimp only [rankCredit_eq] at Hcredit
  iframe Hcredit
  ipureintro
  rfl

/-- Supporting typed Bernoulli specification for a bounded integer threshold. -/
theorem threshold_distSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&Occil.uniformInt #int (b : ℤ) < #int (a : ℤ))
      (RealCoin.law (bias a b hb hab)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_threshold E a b hb hab F)

end specification

end

end SampLib.IntegerThreshold
