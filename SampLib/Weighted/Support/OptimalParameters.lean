import SampLib.Weighted.Syntax.Optimal
import SampLib.Weighted.Laws.OptimalParameters

/-! # Symbolic execution of the cyclic denominator search -/

open ProbLang

namespace SampLib.Optimal

def parameterValue {rT : Type} (p : ℕ × ℕ) : Val rT :=
  Val.pair (Val.int p.1) (Val.int p.2)

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem eq_test (a b : ℕ) (h : a = b) : ((a : ℤ) == b) = true := by simp [h]

private theorem ne_test (a b : ℕ) (h : a ≠ b) : ((a : ℤ) == b) = false := by
  apply beq_eq_false_iff_ne.mpr
  exact_mod_cast h

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open OptimalEncoding

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The actual search evaluates to its terminating integer counterpart. -/
theorem twp_parameters (E : CoPset) (k total l bestL bestTotal : ℕ) :
    ⊢ tglWp E pl(&(Program.parameters k total : Exp rT)
      #int (l : ℤ) #int (bestL : ℤ) #int (bestTotal : ℤ))
      (fun v : Val rT => iprop(⌜v = parameterValue
        (OptimalParameters.select k total l bestL bestTotal)⌝)) := by
  rw [OptimalParameters.select]
  dsimp only
  simp only [OptimalEncoding.denominator]
  by_cases hkl : k ≤ l
  · simp only [hkl, ↓reduceDIte]
    iterate 5 twp_pure
    rw [decide_eq_true (show (k : ℤ) ≤ l by exact_mod_cast hkl)]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  · simp only [hkl, ↓reduceDIte]
    iterate 5 twp_pure
    rw [decide_eq_false (show ¬(k : ℤ) ≤ l by exact_mod_cast hkl)]
    twp_pure
    twp_bind pl(&Occil.Weighted.integerPower #2 #int (l : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply WeightedIntegerPower.twp_integerPower E 2 l
    iintro %v %hv
    subst v
    rw [show (2 : ℤ) ^ l = ((2 ^ l : ℕ) : ℤ) by norm_cast]
    twp_pure
    have hpow : 2 ^ l ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← Nat.cast_sub hpow]
    iterate 2 twp_pure
    rw [int_beq]
    by_cases heq : (2 ^ k - 2 ^ l) = total
    · rw [eq_test _ _ heq]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp only [heq, ite_true, parameterValue]
      subst total
      rfl
    · rw [ne_test _ _ heq]
      iterate 2 twp_pure
      by_cases hlt : (2 ^ k - 2 ^ l) < total
      · rw [decide_eq_true (show (((2 ^ k - 2 ^ l) : ℕ) : ℤ) < total by exact_mod_cast hlt)]
        twp_pures
        twp_value
        imodintro
        ipureintro
        simp only [heq, ite_false, hlt, ite_true, parameterValue]
      · rw [decide_eq_false
          (show ¬(((2 ^ k - 2 ^ l) : ℕ) : ℤ) < total by exact_mod_cast hlt)]
        iterate 2 twp_pure
        rw [show (l : ℤ) + 1 = ((l + 1 : ℕ) : ℤ) by norm_cast]
        simp only [heq, ite_false, hlt]
        ieval (
          change _ ⊢ tglWp E pl(&(Program.parameters k total : Exp rT)
            #int ((l + 1 : ℕ) : ℤ) #int (l : ℤ) #int (((2 ^ k - 2 ^ l) : ℕ) : ℤ)) _)
        iapply twp_parameters E k total (l + 1) l ((2 ^ k - 2 ^ l))
termination_by k - l

end specification

end SampLib.Optimal
