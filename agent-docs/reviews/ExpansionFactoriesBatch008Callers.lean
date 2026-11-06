import SampLib.Constants.ContinuedFraction
import SampLib.Bernoulli.Gambler
import SampLib.Bernoulli.HighPowerLogistic
import SampLib.Templates
import Metrology.Iris.LocalBI

open ProbLang
open scoped ENNReal NNReal

namespace ExpansionFactoriesReview

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial


variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (p : unitInterval) (height : ℕ) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (Gambler.gambler_distSpec E p height a b ha hb coin hc) F I

example (E : CoPset) (p : unitInterval) (height : ℕ) (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (HighPowerLogistic.highPowerLogistic_distSpec E p height a b ha hb coin hc) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (coin : Val rT) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (Gambler.gambler_base_distSpec E coin (-2) (-7) 0 (by decide)) F I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (coin : Val rT) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (HighPowerLogistic.highPowerLogistic_base_distSpec E coin (-2) (-7) 0 (by decide)) F I

example (p : unitInterval) : (Gambler.bias p 1 1 (by decide) (by decide) 0 : ℝ) = 0 := by
  simp [Gambler.bias]
example (p : unitInterval) : (Gambler.bias p 1 1 (by decide) (by decide) 1 : ℝ) = 0 := by
  simp [Gambler.bias]
example : (Gambler.bias 0 1 1 (by decide) (by decide) 4 : ℝ) = 0 := by
  norm_num [Gambler.bias, Gambler.ratio, FiniteGeometricWalk.bias,
    FiniteGeometricWalk.tail, FiniteGeometricWalk.total,
    Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
example : (Gambler.bias 1 1 1 (by decide) (by decide) 4 : ℝ) = 3/4 := by
  norm_num [Gambler.bias, Gambler.ratio, FiniteGeometricWalk.bias,
    FiniteGeometricWalk.tail, FiniteGeometricWalk.total]
example : (Gambler.bias 1 2 1 (by decide) (by decide) 3 : ℝ) = 6/7 := by
  norm_num [Gambler.bias, Gambler.ratio, FiniteGeometricWalk.bias,
    FiniteGeometricWalk.tail, FiniteGeometricWalk.total,
    Finset.sum_Ico_eq_sub, Finset.sum_range_succ]

example (p : unitInterval) :
    (HighPowerLogistic.bias p 1 1 (by decide) (by decide) 0 : ℝ) = 1 := by
  simp [HighPowerLogistic.bias]
example : (HighPowerLogistic.bias 0 1 1 (by decide) (by decide) 3 : ℝ) = 0 := by
  norm_num [HighPowerLogistic.bias, Gambler.ratio, FiniteGeometricWalk.bias,
    FiniteGeometricWalk.tail, FiniteGeometricWalk.total,
    Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
example : (HighPowerLogistic.bias 1 1 1 (by decide) (by decide) 3 : ℝ) = 1/4 := by
  norm_num [HighPowerLogistic.bias, Gambler.ratio, FiniteGeometricWalk.bias,
    FiniteGeometricWalk.tail, FiniteGeometricWalk.total]
example : (HighPowerLogistic.bias 1 2 1 (by decide) (by decide) 2 : ℝ) = 4/7 := by
  norm_num [HighPowerLogistic.bias, Gambler.ratio, FiniteGeometricWalk.bias,
    FiniteGeometricWalk.tail, FiniteGeometricWalk.total,
    Finset.sum_Ico_eq_sub, Finset.sum_range_succ]

example : RealCoin.credit (Gambler.bias 0 1 1 (by decide) (by decide) 4)
    (fun b => if b then ∞ else 0) = 0 := by
  have h : Gambler.bias 0 1 1 (by decide) (by decide) 4 = 0 := by
    apply Subtype.ext
    norm_num [Gambler.bias, Gambler.ratio, FiniteGeometricWalk.bias,
      FiniteGeometricWalk.tail, FiniteGeometricWalk.total,
    Finset.sum_Ico_eq_sub, Finset.sum_range_succ]
  rw [h]
  simp [RealCoin.credit, RealCoin.pmf]

example (p : unitInterval) :
    RealCoin.credit (HighPowerLogistic.bias p 1 1 (by decide) (by decide) 0)
      (fun b => if b then 0 else ∞) = 0 := by
  simp [HighPowerLogistic.bias,
    RealCoin.credit, RealCoin.pmf]

example (t : ℝ) (N i : ℕ) :
    ENNReal.ofReal (FiniteGeometricWalk.work t N i) *
        FiniteGeometricWalk.initialSlack t N i ∞ +
      FiniteGeometricWalk.initialSlack t N i ∞ = ∞ :=
  FiniteGeometricWalk.initialSlack_budget t N i ∞

example (E : CoPset) (a : ℕ → ContinuedFraction.Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hc : ∀ i, ContinuedFraction.Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = ContinuedFraction.encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ContinuedFraction.generalizedContinuedFraction_distSpec E a start coefficient hc) F I

private def terminalOne : ContinuedFraction.Coefficient := ⟨1,1,by decide,by decide,true⟩
private def terminalHalf : ContinuedFraction.Coefficient := ⟨1,2,by decide,by decide,true⟩
private def firstCoefficient : ContinuedFraction.Coefficient := ⟨1,1,by decide,by decide,false⟩
private def finiteFraction (i : ℕ) : ContinuedFraction.Coefficient :=
  if i = 0 then firstCoefficient else terminalHalf

private theorem finite_tail : ContinuedFraction.value finiteFraction 1 =
    (⟨1/2,by norm_num,by norm_num⟩ : unitInterval) := by
  apply Subtype.ext
  rw [ContinuedFraction.value_coe]
  norm_num [finiteFraction, terminalHalf]

example : (ContinuedFraction.value finiteFraction 0 : ℝ) = 2/3 := by
  rw [ContinuedFraction.value_coe]
  norm_num [finiteFraction, firstCoefficient, finite_tail]

private theorem terminal_value : ContinuedFraction.value (fun _ => terminalOne) 0 = 1 := by
  apply Subtype.ext
  rw [ContinuedFraction.value_coe]
  norm_num [terminalOne]

example : RealCoin.credit (ContinuedFraction.value (fun _ => terminalOne) 0)
    (fun b => if b then 0 else ∞) = 0 := by
  rw [terminal_value]
  simp [RealCoin.credit, RealCoin.pmf]

private theorem finite_reachable {i : ℕ}
    (hi : ContinuedFraction.Reachable finiteFraction 0 i) : i = 0 ∨ i = 1 := by
  by_contra h
  have hi2 : 1 < i := by omega
  have hlast := hi.2 1 (by omega) hi2
  simp [finiteFraction, terminalHalf] at hlast

private def finiteOracle {rT : Type} : Val rT :=
  ⟨pl(fun i, if i = #0 then (#1, (#1, #false)) else
    if i = #1 then (#1, (#2, #true)) else fail), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem finite_oracle_spec (E : CoPset) (i : ℕ)
    (hi : ContinuedFraction.Reachable finiteFraction 0 i) :
    ⊢ tglWp E pl(&(finiteOracle (rT := rT)).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = ContinuedFraction.encodeCoefficient (finiteFraction i)⌝)) := by
  obtain rfl | rfl := finite_reachable hi
  · twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  · twp_pures
    twp_value
    imodintro
    ipureintro
    rfl

-- The oracle deliberately fails beyond the final coefficient.
example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ContinuedFraction.generalizedContinuedFraction_distSpec E finiteFraction 0
    (finiteOracle (rT := rT)) (finite_oracle_spec E)) F I

example (a : ℕ → ContinuedFraction.Coefficient) (i : ℕ) :=
  ContinuedFraction.recursive_budget a i

#print axioms SampLib.ContinuedFraction.generalizedContinuedFraction_distSpec
#print axioms SampLib.ContinuedFraction.expectation
#print axioms SampLib.ContinuedFraction.unique_value
#print axioms SampLib.ContinuedFraction.recursive_budget

example (E : CoPset) (a : ℕ → SimpleContinuedFraction.Coefficient)
    (coefficient : Val rT)
    (hc : ∀ i, ContinuedFraction.Reachable (SimpleContinuedFraction.sequence a) 1 i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = SimpleContinuedFraction.encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (SimpleContinuedFraction.continuedFraction_distSpec E a coefficient hc) F I

private def simpleLast : SimpleContinuedFraction.Coefficient := ⟨1,by decide,true⟩
private theorem simple_terminal : SimpleContinuedFraction.bias (fun _ => simpleLast) = 1 := by
  apply Subtype.ext
  rw [ContinuedFraction.value_coe]
  norm_num [SimpleContinuedFraction.sequence, SimpleContinuedFraction.Coefficient.generalized,
    simpleLast]
example : RealCoin.credit (SimpleContinuedFraction.bias (fun _ => simpleLast))
    (fun b => if b then 0 else ∞) = 0 := by
  rw [simple_terminal]
  simp [RealCoin.credit, RealCoin.pmf]

#print axioms SampLib.SimpleContinuedFraction.continuedFraction_distSpec
#print axioms SampLib.SimpleContinuedFraction.twp_continuedFraction

#print axioms SampLib.Gambler.gambler_distSpec
#print axioms SampLib.Gambler.gambler_base_distSpec
#print axioms SampLib.HighPowerLogistic.highPowerLogistic_distSpec
#print axioms SampLib.HighPowerLogistic.highPowerLogistic_base_distSpec
#print axioms SampLib.FiniteGeometricWalk.credit_harmonic
#print axioms SampLib.FiniteGeometricWalk.work_drift
#print axioms SampLib.FiniteGeometricWalk.expectation
#print axioms SampLib.FiniteGeometricWalk.initialSlack_budget

end
end ExpansionFactoriesReview
