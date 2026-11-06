import SampLib.Bernoulli.FractionalPower
import SampLib.Bernoulli.CoinProduct
import SampLib.Common.FactorySyntax
import SampLib.Common.Laws.RationalPower
import Samplers.Bernoulli.Powers
import Samplers.Discrete.Tails

/-! # Nonnegative rational powers of an abstract input coin

Integer successes and the residual fractional power multiply to the full power.
The zero-remainder branch never calls the fractional engine.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RationalPower

noncomputable section

/-- The Bernoulli bias for a nonnegative rational power. -/
def bias (p : unitInterval) (a b : ℕ) (_hb : 0 < b) : unitInterval :=
  ⟨(p : ℝ) ^ ((a : ℝ) / b : ℝ), Real.rpow_nonneg p.2.1 _,
    Real.rpow_le_one p.2.1 p.2.2 (by positivity)⟩

private def suffixBias (p : unitInterval) (a b : ℕ) : unitInterval :=
  ⟨(p : ℝ) ^ ((a % b : ℕ) / (b : ℝ) : ℝ), Real.rpow_nonneg p.2.1 _,
    Real.rpow_le_one p.2.1 p.2.2 (by positivity)⟩

private theorem bias_product (p : unitInterval) (a b : ℕ) (hb : 0 < b) :
    IterateCoin.bias p (a / b) * suffixBias p a b = bias p a b hb := by
  apply Subtype.ext
  exact power_split p.2.1 a b hb

private def firstCredit (p : unitInterval) (a b : ℕ) (F : Bool → ℝ≥0∞)
    (bit : Bool) : ℝ≥0∞ := if bit then RealCoin.credit (suffixBias p a b) F else F false

/-- The quotient/remainder decomposition preserves arbitrary continuation credits. -/
theorem expectation (p : unitInterval) (a b : ℕ) (hb : 0 < b) (F : Bool → ℝ≥0∞) :
    ∫⁻ bit, firstCredit p a b F bit ∂IterateCoin.law p (a / b) =
      RealCoin.credit (bias p a b hb) F := by
  simpa only [CoinProduct.firstCredit, firstCredit, CoinProduct.law,
    RealCoin.lintegral_law, bias_product p a b hb] using
    CoinProduct.expectation_preservation (IterateCoin.bias p (a / b)) (suffixBias p a b) F

private theorem suffix_zero (p : unitInterval) (a b : ℕ) (h : a % b = 0)
    (F : Bool → ℝ≥0∞) : RealCoin.credit (suffixBias p a b) F = F true := by
  simp [suffixBias, h, RealCoin.credit, RealCoin.pmf]

private theorem suffix_fractional (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (h : a % b ≠ 0) :
    suffixBias p a b = FractionalPower.bias p (a % b) b (Nat.pos_of_ne_zero h)
      (Nat.mod_lt a hb).le := rfl

private def source {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.rationalPower, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source : Val rT).fst = Occil.FactoryExtra.rationalPower := rfl

private def discreteSource {rT : Type} : Val rT :=
  ⟨Occil.DiscreteExtra.rationalPowerCoin, .lam (by is_lc), by is_lc⟩

private theorem discreteSource_fst {rT : Type} :
    (discreteSource : Val rT).fst = Occil.DiscreteExtra.rationalPowerCoin := rfl

private theorem int_nonzero {rT : Type} [BEq rT] (a : ℤ) (ha : a ≠ 0) :
    ((BaseLit.int a : BaseLit rT) == .int 0) = false := by
  change (a == 0) = false
  exact beq_eq_false_iff_ne.mpr ha

private theorem valid_denominator (b : ℕ) (hb : 0 < b) :
    decide ((b : ℤ) ≤ 0) = false := by
  simp only [decide_eq_false_iff_not, not_le]
  exact_mod_cast hb

private theorem remainder_nonzero {rT : Type} [BEq rT] (a b : ℕ) (h : a % b ≠ 0) :
    ((BaseLit.int ((a % b : ℕ) : ℤ) : BaseLit rT) == .int 0) = false :=
  int_nonzero _ (by exact_mod_cast h)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Every nonnegative numerator and positive denominator, including both input-coin endpoints. -/
theorem rationalPower_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.rationalPower &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias p a b hb)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    twp_pures
    simp only [valid_denominator b hb, Bool.false_or, FactorySyntax.iterateCoin_openRec,
      FactorySyntax.iterateCoin_closeRec]
    twp_pure
    twp_pure
    rw [← Int.natCast_ediv]
    twp_bind pl(&Occil.iterateCoin &coin.fst #int ((a / b : ℕ) : ℤ))
    isimp only [RealCoin.lintegral_law] at Hcredit
    isimp only [← expectation p a b hb F] at Hcredit
    iapply ((IterateCoin.iterateCoin_distSpec E p coin hcoin (a / b)).wp
      (firstCredit p a b F) (measurable_of_countable _) _) $$ Hcredit
    iintro %bit Hcredit
    cases bit
    · isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      itrivial
    · isimp only [firstCredit, ite_true] at Hcredit
      twp_pures
      rw [← Int.natCast_emod]
      by_cases hzero : a % b = 0
      · rw [hzero]
        twp_pures
        twp_value
        imodintro
        iexists true
        isimp only [suffix_zero p a b hzero F] at Hcredit
        iframe Hcredit
        itrivial
      · rw [remainder_nonzero (rT := rT) a b hzero]
        twp_pure
        isimp only [FractionalPower.Program.fractionalPower_openRec,
          FractionalPower.Program.fractionalPower_closeRec]
        twp_pure
        rw [← Int.natCast_emod]
        isimp only [Exp.ofVal]
        isimp only [suffix_fractional p a b hb hzero, ← RealCoin.lintegral_law] at Hcredit
        iapply ((FractionalPower.fractionalPower_distSpec E p (a % b) b
          (Nat.pos_of_ne_zero hzero) (Nat.mod_lt a hb).le coin hcoin).spec
          F (measurable_of_countable _)) $$ Hcredit

/-- The discrete-sampler variant caches the same remainder before dispatch. -/
theorem rationalPowerCoin_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.rationalPowerCoin &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias p a b hb)) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← discreteSource_fst (rT := rT)]
    twp_pures
    simp only [valid_denominator b hb, Bool.false_or, FactorySyntax.iterateCoin_openRec,
      FactorySyntax.iterateCoin_closeRec]
    twp_pure
    twp_pure
    rw [← Int.natCast_ediv]
    twp_bind pl(&Occil.iterateCoin &coin.fst #int ((a / b : ℕ) : ℤ))
    isimp only [RealCoin.lintegral_law] at Hcredit
    isimp only [← expectation p a b hb F] at Hcredit
    iapply ((IterateCoin.iterateCoin_distSpec E p coin hcoin (a / b)).wp
      (firstCredit p a b F) (measurable_of_countable _) _) $$ Hcredit
    iintro %bit Hcredit
    cases bit
    · isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      itrivial
    · isimp only [firstCredit, ite_true] at Hcredit
      twp_pures
      rw [← Int.natCast_emod]
      by_cases hzero : a % b = 0
      · rw [hzero]
        twp_pures
        twp_value
        imodintro
        iexists true
        isimp only [suffix_zero p a b hzero F] at Hcredit
        iframe Hcredit
        itrivial
      · rw [remainder_nonzero (rT := rT) a b hzero]
        twp_pure
        isimp only [FractionalPower.Program.fractionalPower_openRec,
          FractionalPower.Program.fractionalPower_closeRec]
        isimp only [suffix_fractional p a b hb hzero, ← RealCoin.lintegral_law] at Hcredit
        iapply ((FractionalPower.fractionalPower_distSpec E p (a % b) b
          (Nat.pos_of_ne_zero hzero) (Nat.mod_lt a hb).le coin hcoin).spec
          F (measurable_of_countable _)) $$ Hcredit

end specification

end

end SampLib.RationalPower
