import SampLib.Weighted.Laws.FloatingMultiply
import SampLib.Core.SamplerStep
import SampLib.Weighted.Support.RoundBinary
import SampLib.Weighted.RandomBits
import SampLib.Weighted.Laws.FiniteImage

/-! # Integer-emulated floating multiplication

A finite uniform binary word is multiplied, rounded to an unbounded-exponent
binary significand with nearest/even ties, and divided by the word modulus.
The finite law records rounding and division bias; no hardware IEEE or continuous law is asserted.
The outer-valid corner bits=precision=0, n=1 uses an invalid rounding format:
`RoundBinary.zero_precision_fails` shows that the helper fails for every sampled word.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.FloatingMultiply

noncomputable section

private def source {rT : Type} : Val rT :=
  ⟨Occil.WeightedVariants.floatingMultiply, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source (rT := rT)).fst = Occil.WeightedVariants.floatingMultiply := rfl

private theorem valid_test (n bits precision : ℕ) (hn : 0 < n) (hbound : n ≤ 2 ^ bits)
    (hp : bits ≤ precision) :
    ((decide ((n : ℤ) ≤ 0) || decide (((2 ^ bits : ℕ) : ℤ) < (n : ℤ))) ||
      decide ((precision : ℤ) < (bits : ℤ))) = false := by
  have hb : (n : ℤ) ≤ (2 : ℤ) ^ bits := by exact_mod_cast hbound
  simp [hn.ne', not_lt.mpr hb, show ¬(precision : ℤ) < bits by omega]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Exact finite rounding law on the full valid natural binary-format domain.
Positive precision is essential, including when bits=0 and n=1. -/
theorem floatingMultiply_distSpec (E : CoPset) (n bits precision : ℕ)
    (hn : 0 < n) (hbound : n ≤ 2 ^ bits) (hp : 0 < precision) (hbp : bits ≤ precision) :
    IsDistSpec (GF := GF) E
      pl(&Occil.WeightedVariants.floatingMultiply #int (n : ℤ)
        #int (bits : ℤ) #int (precision : ℤ)) (law n bits precision)
      (fun x : ℕ => Val.int (x : ℤ)) where
  spec F _ := by
    have hpower := WeightedIntegerPower.twp_integerPower (rT := rT) (GF := GF) E 2 bits
    have hcast : (2 : ℤ) ^ bits = ((2 ^ bits : ℕ) : ℤ) := by simp
    rw [hcast] at hpower
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 3 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, WeightedIntegerPower.integerPower_openRec,
      WeightedIntegerPower.integerPower_closeRec, RandomBits.randomBits_openRec,
      RandomBits.randomBits_closeRec, ClosedExp.openRec, ClosedExp.closeRec])
    twp_bind pl(&Occil.Weighted.integerPower #2 #int (bits : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hpower
    iintro %v %hv
    subst v
    twp_pures
    rw [valid_test n bits precision hn hbound hbp]
    twp_pure
    simp only [RandomBits.randomBits_openRec, ClosedExp.openRec]
    twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
    isimp only [law, ← FiniteImage.expectation] at Hcredit
    iapply ((RandomBits.randomBits_distSpec E bits).wp
      (fun word => F (output n bits precision word))
      (measurable_of_countable _) _) $$ Hcredit
    iintro %word Hcredit
    twp_pure
    have hround := RoundBinary.twp_roundBinary (rT := rT) (GF := GF) E (n * word) precision hp
    rw [Int.natCast_mul] at hround
    twp_bind pl(&Occil.WeightedVariants.roundBinary #int ((n : ℤ) * word) #int (precision : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hround
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    iexists output n bits precision word
    iframe Hcredit
    ipureintro
    apply Val.ext
    simp only [output, Int.natCast_div]

end specification

end

end SampLib.FloatingMultiply
