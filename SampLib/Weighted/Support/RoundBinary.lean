import SampLib.Weighted.Support.BitLength
import SampLib.Weighted.Support.WeightedIntegerPower
import Samplers.Weighted.Reductions

/-! # Exact integer-emulated binary rounding

This deterministic helper has an unbounded exponent and nearest/even ties.
Precision zero is an invalid format and reaches the source's failure guard.
-/

open ProbLang

namespace SampLib.RoundBinary

private theorem valid_test (precision : ℕ) (hp : 0 < precision) :
    (false || decide ((precision : ℤ) ≤ 0)) = false := by simp; omega

private theorem fit_test (value precision : ℕ) :
    decide ((value.size : ℤ) ≤ (precision : ℤ)) = decide (value.size ≤ precision) := by simp

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem rounding_test (value q : ℕ) :
    (decide ((q : ℤ) < 2 * ((value : ℤ) % q)) ||
      (((q : ℤ) == 2 * ((value : ℤ) % q)) && (((value : ℤ) / q) % 2 == 1))) =
        decide (q < 2 * (value % q) ∨ q = 2 * (value % q) ∧ (value / q) % 2 = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [← Int.natCast_div, ← Int.natCast_mod]
  norm_cast

private theorem up_result (value precision : ℕ) (hf : ¬value.size ≤ precision)
    (hu : BinaryRounding.quantum value precision <
      2 * (value % BinaryRounding.quantum value precision) ∨
      BinaryRounding.quantum value precision =
        2 * (value % BinaryRounding.quantum value precision) ∧
        (value / BinaryRounding.quantum value precision) % 2 = 1) :
    (((value : ℤ) / BinaryRounding.quantum value precision + 1) *
      BinaryRounding.quantum value precision) = (BinaryRounding.round value precision : ℤ) := by
  rw [BinaryRounding.round, ite_eq_right hf]
  dsimp only
  rw [ite_eq_left hu]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Int.natCast_div]

private theorem down_result (value precision : ℕ) (hf : ¬value.size ≤ precision)
    (hu : ¬(BinaryRounding.quantum value precision <
      2 * (value % BinaryRounding.quantum value precision) ∨
      BinaryRounding.quantum value precision =
        2 * (value % BinaryRounding.quantum value precision) ∧
        (value / BinaryRounding.quantum value precision) % 2 = 1)) :
    ((value : ℤ) / BinaryRounding.quantum value precision *
      BinaryRounding.quantum value precision) =
      (BinaryRounding.round value precision : ℤ) := by
  rw [BinaryRounding.round, ite_eq_right hf]
  dsimp only
  rw [ite_eq_right hu]
  simp only [Nat.cast_mul, Int.natCast_div]

instance roundBinary_closed {rT : Type} :
    ClosedExp (Occil.WeightedVariants.roundBinary : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.WeightedVariants.roundBinary, Exp.fv, ClosedExp.closeRec, ClosedExp.fv,
    WeightedIntegerPower.integerPower_fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The source realizes exact nearest/even integer rounding for every positive precision. -/
theorem twp_roundBinary (E : CoPset) (value precision : ℕ) (hp : 0 < precision) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.roundBinary #int (value : ℤ) #int (precision : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (BinaryRounding.round value precision : ℤ)⌝)) := by
  twp_pures
  rw [valid_test precision hp]
  twp_pure
  twp_bind pl(&Occil.WeightedVariants.bitLength #int (value : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply BitLength.twp_bitLength E value
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  rw [fit_test]
  by_cases hf : value.size ≤ precision
  · simp only [hf, decide_true]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [BinaryRounding.round_exact value precision hf]
  · simp only [hf, decide_false]
    iterate 2 twp_pure
    have hle : precision ≤ value.size := by omega
    have hpower := WeightedIntegerPower.twp_integerPower (rT := rT) (GF := GF)
      E 2 (value.size - precision)
    rw [Int.natCast_sub hle] at hpower
    have hcast : (2 : ℤ) ^ (value.size - precision) =
        (BinaryRounding.quantum value precision : ℤ) := by simp [BinaryRounding.quantum]
    rw [hcast] at hpower
    twp_bind pl(&Occil.Weighted.integerPower #2 #int ((value.size : ℤ) - precision))
    iapply tglWp_wand
    isplitl []
    · iapply hpower
    iintro %q %hq
    subst q
    twp_pures
    simp only [int_beq]
    rw [rounding_test]
    by_cases hu : BinaryRounding.quantum value precision <
        2 * (value % BinaryRounding.quantum value precision) ∨
        BinaryRounding.quantum value precision =
        2 * (value % BinaryRounding.quantum value precision) ∧
          (value / BinaryRounding.quantum value precision) % 2 = 1
    · simp only [hu, decide_true]
      twp_pures
      twp_value
      imodintro
      ipureintro
      exact congrArg Val.int (up_result value precision hf hu)
    · simp only [hu, decide_false]
      twp_pures
      twp_value
      imodintro
      ipureintro
      exact congrArg Val.int (down_result value precision hf hu)

/-- The invalid zero-precision format really reduces to failure. -/
theorem zero_precision_fails (value : ℕ) :
    PureSteps (pl(&Occil.WeightedVariants.roundBinary #int (value : ℤ) #0) : Exp rT) pl(fail) := by
  pure_steps

end specification

end SampLib.RoundBinary
