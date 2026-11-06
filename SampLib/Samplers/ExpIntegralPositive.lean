import SampLib.Distributions.ExpIntegral
import SampLib.Samplers.ExpMinusShifted
import Samplers.Bernoulli.Elementary

/-! # The positive integer-shift branch of the factorial-integral coin -/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpIntegral

noncomputable section

private theorem zero_test {rT : Type} [BEq rT] (m : ℕ) (hm : 0 < m) :
    ((BaseLit.int (m : ℤ) : BaseLit rT) == .int 0) = false := by
  change decide ((m : ℤ) = 0) = false
  exact decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ExpMinusShifted.expMinusShifted_openRec
  ExpMinusShifted.expMinusShifted_closeRec ReciprocalAffine.reciprocalAffine_openRec
  ReciprocalAffine.reciprocalAffine_closeRec

private theorem reciprocal_spec (E : CoPset) (p : unitInterval) (m : ℕ) (hm : 0 < m)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.reciprocalAffine &coin.fst #int (m : ℤ) #1 #1 #1 #())
      (RealCoin.law (reciprocal p m hm)) Val.bool := by
  simpa only [Nat.mul_one, Nat.one_mul, Nat.cast_one] using
    ReciprocalAffine.reciprocalAffine_distSpec E p m 1 1 1 hm (by decide) (by decide)
      (by omega) coin hcoin

private theorem shifted_spec (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.expMinusShifted &coin.fst #int (m : ℤ) #1 #())
      (RealCoin.law (shifted p m)) Val.bool :=
  ExpMinusShifted.expMinusShifted_distSpec E p m 1 (Int.natCast_nonneg _)
    (by decide) coin hcoin

/-- Execute the two independently specified factories at every positive integer shift. -/
theorem twp_expIntegral_positive (E : CoPset) (p : unitInterval) (m : ℕ) (hm : 0 < m)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (positiveBias p m hm)) -∗
      tglWp E pl(&Occil.FactoryExtra.expIntegral &coin.fst #int (m : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 6 twp_pure
  rw [zero_test m hm]
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.expMinusShifted &coin.fst #int (m : ℤ) #1 #())
  isimp only [← expectation_positive p m hm F] at Hcredit
  iapply ((shifted_spec E p m coin hcoin).wp (firstCredit p m hm F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pure
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (reciprocal_spec E p m hm coin hcoin).spec F (measurable_of_countable _) $$ Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [firstCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

end specification

end

end SampLib.ExpIntegral
