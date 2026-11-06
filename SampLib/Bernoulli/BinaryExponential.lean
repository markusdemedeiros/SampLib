import SampLib.Bernoulli.BinaryExponentialRational
import SampLib.Bernoulli.Support.FactoryIntegerPower

/-! # An integer shift of the binary-exponential factory -/

open ProbLang
open scoped ENNReal

namespace SampLib.BinaryExponential

noncomputable section

private def selector (m k : ℕ) : unitInterval :=
  RationalCoin.bias 1 (2 ^ (m * k)) (by decide)
    (pow_pos (by decide) _) (one_le_pow₀ (by decide))

abbrev bias (p : unitInterval) (m k : ℕ) : unitInterval :=
  selector m k * BinaryExponentialRational.bias p m 1

theorem bias_coe (p : unitInterval) (m k : ℕ) :
    (bias p m k : ℝ) = (2 : ℝ) ^ (-(m : ℝ) * (k + p)) := by
  simp only [bias, Set.Icc.coe_mul, selector, RationalCoin.bias,
    BinaryExponentialRational.bias_coe, Int.cast_one, Int.cast_pow, Int.cast_ofNat,
    Nat.cast_one, div_one]
  rw [show -(m : ℝ) * ((k : ℝ) + p) = -((m * k : ℕ) : ℝ) + -(m : ℝ) * p by
    push_cast; ring, Real.rpow_add (by norm_num),
    Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private instance power_closed : ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

private theorem selector_spec (E : CoPset) (m k : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #1 #int ((2 : ℤ) ^ (m * k)))
      (RealCoin.law (selector m k)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by decide)
    (pow_pos (by decide) _) (one_le_pow₀ (by decide))

/-- The rational prefactor pays for the integer shift; thinning supplies the fractional shift. -/
theorem twp_binaryExponential (E : CoPset) (p : unitInterval) (m k : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias p m k)) -∗
      tglWp E pl(&Occil.FactoryExtra.binaryExponential &coin.fst
        #int (m : ℤ) #int (k : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 8 twp_pure
  simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.FactoryExtra.intPower #2 (#int (m : ℤ) * #int (k : ℤ)))
  twp_pure
  rw [← Nat.cast_mul]
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower E 2 (m * k)
  iintro %v %hv
  subst v
  isimp only [Exp.ofVal]
  twp_bind pl(&Occil.rationalCoin #1 #int ((2 : ℤ) ^ (m * k)))
  isimp only [← CoinProduct.expectation_preservation (selector m k)
    (BinaryExponentialRational.bias p m 1) F] at Hcredit
  iapply ((selector_spec E m k).wp
    (CoinProduct.firstCredit (BinaryExponentialRational.bias p m 1) F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pure
    isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
    have hsample := (ExpMinusScaled.expMinusScaled_distSpec E
      (p * BinaryExponentialRational.logTwo) m 1 (by decide)
      (BinaryExponentialRational.logarithmCallback coin)
      (BinaryExponentialRational.logarithmCallback_distSpec E p coin hcoin)).spec F
      (measurable_of_countable _)
    simp only [BinaryExponentialRational.logarithmCallback] at hsample
    iapply hsample $$ Hcredit

theorem binaryExponential_distSpec (E : CoPset) (p : unitInterval) (m k : ℕ)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.binaryExponential &coin.fst #int (m : ℤ) #int (k : ℤ) #())
      (RealCoin.law (bias p m k)) Val.bool where
  spec F _ := wand_entails (twp_binaryExponential E p m k coin hcoin F)

end specification

end

end SampLib.BinaryExponential
