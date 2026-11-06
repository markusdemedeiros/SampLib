import SampLib.Common.RationalPower
import Samplers.PSRN.Uniform

/-! # Rational powers of an abstract coin

The whole and residual powers multiply by quotient/remainder factorization.
A zero residual returns immediately, including the convention `0^0 = 1`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNPowerCoin

noncomputable section

private theorem bias_product (p : unitInterval) (a b : ℕ) (hb : 0 < b) :
    IterateCoin.bias p (a / b) * RationalPower.bias p (a % b) b hb =
      RationalPower.bias p a b hb := by
  apply Subtype.ext
  exact RationalPower.power_split p.2.1 a b hb

/-- Whole successes followed by the residual trial preserve the full rational-power law. -/
theorem expectation (p : unitInterval) (a b : ℕ) (hb : 0 < b) (F : Bool → ℝ≥0∞) :
    (∫⁻ bit, CoinProduct.firstCredit (RationalPower.bias p (a % b) b hb) F bit
      ∂IterateCoin.law p (a / b)) =
      ∫⁻ bit, F bit ∂RealCoin.law (RationalPower.bias p a b hb) := by
  simpa only [CoinProduct.law, bias_product p a b hb] using
    CoinProduct.expectation_preservation (IterateCoin.bias p (a / b))
      (RationalPower.bias p (a % b) b hb) F

private theorem zero_credit (p : unitInterval) (b : ℕ) (hb : 0 < b) (F : Bool → ℝ≥0∞) :
    (∫⁻ bit, F bit ∂RealCoin.law (RationalPower.bias p 0 b hb)) = F true := by
  simp [RealCoin.lintegral_law, RationalPower.bias, RealCoin.credit, RealCoin.pmf]

private theorem residual_fractional (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (h : a % b ≠ 0) :
    RationalPower.bias p (a % b) b hb =
      FractionalPower.bias p (a % b) b (Nat.pos_of_ne_zero h) (Nat.mod_lt a hb).le := rfl

private def source {rT : Type} : Val rT :=
  ⟨Occil.PSRN.powerCoin, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.PSRN.powerCoin := rfl

private theorem valid_denominator (b : ℕ) (hb : 0 < b) :
    decide ((b : ℤ) ≤ 0) = false := by
  simp only [decide_eq_false_iff_not, not_le]
  exact_mod_cast hb

private theorem remainder_nonzero {rT : Type} [BEq rT] (a b : ℕ) (h : a % b ≠ 0) :
    ((BaseLit.int ((a % b : ℕ) : ℤ) : BaseLit rT) == .int 0) = false := by
  change (((a % b : ℕ) : ℤ) == 0) = false
  exact beq_eq_false_iff_ne.mpr (by exact_mod_cast h)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Execute the integer and residual engines under their existing specifications. -/
theorem twp_powerCoin (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ bit, F bit ∂RealCoin.law (RationalPower.bias p a b hb)) -∗
      tglWp E pl(&Occil.PSRN.powerCoin &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun result : Val rT => iprop(∃ bit : Bool, ⌜result = Val.bool bit⌝ ∗ ↯ (F bit))) := by
  iintro Hcredit
  rw [← source_fst (rT := rT)]
  twp_pures
  rw [valid_denominator b hb, Bool.false_or]
  twp_pure
  isimp only [FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec]
  twp_pure
  rw [← Int.natCast_ediv]
  twp_bind pl(&Occil.iterateCoin &coin.fst #int ((a / b : ℕ) : ℤ))
  isimp only [← expectation p a b hb F] at Hcredit
  iapply (IterateCoin.iterateCoin_distSpec E p coin hcoin (a / b)).wp
    (CoinProduct.firstCredit (RationalPower.bias p (a % b) b hb) F)
    (measurable_of_countable _) _ $$ Hcredit
  iintro %whole Hcredit
  cases whole
  · isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists false
    iframe Hcredit
    itrivial
  · isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
    twp_pures
    rw [← Int.natCast_emod]
    by_cases hzero : a % b = 0
    · rw [hzero]
      twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [zero_credit p b hb F] at Hcredit
      iframe Hcredit
      itrivial
    · rw [remainder_nonzero (rT := rT) a b hzero]
      twp_pure
      isimp only [FractionalPower.Program.fractionalPower_openRec,
        FractionalPower.Program.fractionalPower_closeRec]
      isimp only [residual_fractional p a b hb hzero] at Hcredit
      iapply (FractionalPower.fractionalPower_distSpec E p (a % b) b
        (Nat.pos_of_ne_zero hzero) (Nat.mod_lt a hb).le coin hcoin).spec
        F (measurable_of_countable _) $$ Hcredit

/-- The exact source supports every nonnegative numerator and positive denominator. -/
theorem powerCoin_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.PSRN.powerCoin &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (RationalPower.bias p a b hb)) Val.bool where
  spec F _ := wand_entails (twp_powerCoin E p a b hb coin hcoin F)

end specification

end

end SampLib.PSRNPowerCoin
