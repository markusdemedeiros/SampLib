import SampLib.Samplers.RandomBits
import SampLib.WeightedIntegerPower
import SampLib.Distributions.FiniteImage
import Samplers.Weighted.Reductions

/-! # Exact laws of biased word reductions

Modulo and multiply-and-shift have explicit finite laws. Equal output masses
are not assumed: every mass counts its preimages among the source words.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.WordReductions

noncomputable section

private theorem positive_test (n : ℕ) (hn : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := by simp; omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Modulo reduction, including its bias when the target width does not divide `2^bits`. -/
theorem moduloReduction_distSpec (E : CoPset) (n bits : ℕ) (hn : 0 < n) :
    letI : NeZero (2 ^ bits) := ⟨by positivity⟩
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.moduloReduction #int (n : ℤ) #int (bits : ℤ))
      (FiniteImage.law (2 ^ bits) (fun k => k % n))
      (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  twp_pures
  rw [positive_test n hn]
  simp only [Bool.false_or, RandomBits.randomBits_openRec, RandomBits.randomBits_closeRec]
  twp_pure
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  isimp only [← FiniteImage.expectation] at Hcredit
  iapply ((RandomBits.randomBits_distSpec E bits).wp (fun k => F (k % n))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  twp_pures
  twp_value
  imodintro
  iexists k % n
  iframe Hcredit
  ipureintro
  apply Val.ext
  simp only [Int.natCast_mod]

/-- Multiply-and-shift has the finite image law of `floor(k*n/2^bits)`. -/
theorem multiplyShift_distSpec (E : CoPset) (n bits : ℕ) (hn : 0 < n) :
    letI : NeZero (2 ^ bits) := ⟨by positivity⟩
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.multiplyShift #int (n : ℤ) #int (bits : ℤ))
      (FiniteImage.law (2 ^ bits) (fun k => k * n / 2 ^ bits))
      (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  twp_pures
  rw [positive_test n hn]
  simp only [Bool.false_or, WeightedIntegerPower.integerPower_openRec,
    WeightedIntegerPower.integerPower_closeRec, RandomBits.randomBits_openRec,
    RandomBits.randomBits_closeRec]
  twp_pure
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (bits : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 bits
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  isimp only [← FiniteImage.expectation] at Hcredit
  iapply ((RandomBits.randomBits_distSpec E bits).wp (fun k => F (k * n / 2 ^ bits))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  twp_pures
  twp_value
  imodintro
  iexists k * n / 2 ^ bits
  iframe Hcredit
  ipureintro
  apply Val.ext
  simp only [Int.natCast_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

end specification

end

end SampLib.WordReductions
