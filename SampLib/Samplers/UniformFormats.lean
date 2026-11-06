import SampLib.Samplers.RandomBits
import SampLib.WeightedIntegerPower

/-! # Exact uniform grid representations

The random numerator is uniform; denominators and fixed-point scales are explicit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformFormats

noncomputable section

private theorem two_pow_cast (bits : ℕ) :
    (2 : ℤ) ^ bits = ((2 ^ bits : ℕ) : ℤ) := by norm_cast

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Uniform numerator at a caller-supplied positive denominator. -/
theorem uniformRational_distSpec (E : CoPset) (denominator : ℕ) [NeZero denominator] :
    IsDistSpec (GF := GF) E
      pl(&Occil.Weighted.uniformRational #int (denominator : ℤ) #())
      (UniformInt.law denominator)
      (fun k : ℕ => Val.pair (Val.int (k : ℤ)) (Val.int (denominator : ℤ))) where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    twp_bind pl(&Occil.uniformInt #int (denominator : ℤ))
    iapply ((UniformInt.uniformInt_distSpec E denominator).wp F hF _) $$ Hcredit
    iintro %k Hcredit
    twp_value
    imodintro
    iexists k
    iframe Hcredit
    ipureintro
    exact Val.ext rfl

/-- Fixed-point uniforms are uniform integers with an explicit positive scale. -/
theorem uniformFixed_distSpec (E : CoPset) (scale : ℕ) [NeZero scale] :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.uniformFixed #int (scale : ℤ) #())
      (UniformInt.law scale) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
    iapply ((UniformInt.uniformInt_distSpec E scale).wp F hF _) $$ Hcredit
    iintro %k Hcredit
    iexists k
    iframe Hcredit
    ipureintro
    exact Val.ext rfl

/-- The empty binary word represents zero at denominator one. -/
theorem uniformDyadic_distSpec (E : CoPset) (bits : ℕ) :
    letI : NeZero (2 ^ bits) := ⟨by positivity⟩
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.uniformDyadic #int (bits : ℤ) #())
      (UniformInt.law (2 ^ bits))
      (fun k : ℕ => Val.pair (Val.int (k : ℤ)) (Val.int ((2 ^ bits : ℕ) : ℤ))) := by
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  iterate 4 twp_pure
  simp only [WeightedIntegerPower.integerPower_openRec,
    WeightedIntegerPower.integerPower_closeRec, RandomBits.randomBits_openRec,
    RandomBits.randomBits_closeRec]
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (bits : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 bits
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.Weighted.randomBits #int (bits : ℤ))
  iapply ((RandomBits.randomBits_distSpec E bits).wp F hF _) $$ Hcredit
  iintro %k Hcredit
  twp_value
  imodintro
  iexists k
  iframe Hcredit
  ipureintro
  apply Val.ext
  simp only [two_pow_cast]
  rfl

end specification

end

end SampLib.UniformFormats
