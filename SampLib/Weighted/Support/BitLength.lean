import SampLib.Templates
import SampLib.Core.Syntax.ClosedExp
import SampLib.Common.Laws.BinaryRounding
import Samplers.Weighted.Core

/-! # The exact nonnegative integer bit-length helper -/

open ProbLang

namespace SampLib.BitLength

private theorem nonzero_test (n : ℕ) (hn : 0 < n) : ((n : ℤ) == 0) = false := by
  simp
  omega

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

instance bitLength_closed {rT : Type} :
    ClosedExp (Occil.WeightedVariants.bitLength : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.WeightedVariants.bitLength, Exp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The source counts the standard binary digits, with bit length zero at zero. -/
theorem twp_bitLength (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.bitLength #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.size : ℤ)⌝)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      twp_pures
      twp_value
      imodintro
      itrivial
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      twp_pures
      rw [int_beq, nonzero_test n hn']
      iterate 2 twp_pure
      have hrec := ih (n / 2) (Nat.div_lt_self hn' (by decide))
      rw [Int.natCast_div] at hrec
      twp_bind pl(&Occil.WeightedVariants.bitLength #int ((n : ℤ) / 2))
      iapply tglWp_wand
      isplitl []
      · iapply hrec
      iintro %v %hv
      subst v
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply congrArg Val.int
      simp [BinaryRounding.size_step hn']

end specification

end SampLib.BitLength
