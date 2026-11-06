import SampLib.Bernoulli.RationalPowerInteger
import SampLib.Bernoulli.FractionalPower

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped ENNReal

namespace SampLib.ExactPowersCallers

noncomputable section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A caller retains an arbitrary linear resource through the rational-power dispatch. -/
theorem framed_integer_power (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n b : ℕ) (hb : 0 < b) (F : Bool → ℝ≥0∞) (P : IProp GF) :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂IterateCoin.law p n)) ⊢
      tglWp E
        pl(&Occil.FactoryExtra.rationalPower &coin.fst #int ((n * b : ℕ) : ℤ)
          #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((RationalPowerInteger.rationalPower_integer_distSpec E p coin hcoin n b hb).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

/-- Full-domain fractional powers retain the caller's unrelated resource. -/
theorem framed_fractional_power (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) (F : Bool → ℝ≥0∞) (P : IProp GF)
    [ProbLangDist.IsUniformInt rT] :
    iprop(P ∗ ↯ (∫⁻ bit, F bit ∂RealCoin.law (FractionalPower.bias p a b ha hab))) ⊢
      tglWp E pl(&Occil.fractionalPower &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ bit : Bool, ⌜v = Val.bool bit⌝ ∗ P ∗ ↯ (F bit))) := by
  iintro ⟨HP, Hcredit⟩
  iapply ((FractionalPower.fractionalPower_distSpec E p a b ha hab coin hcoin).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  iexists bit
  iframe HP Hcredit
  itrivial

private def constantCoin (bit : Bool) : Val rT :=
  ⟨.lam (.lit (.bool bit)), .lam (by is_lc), by is_lc⟩

private theorem constantCoin_spec (E : CoPset) (bit : Bool) :
    IsDistSpec (GF := GF) E pl(&(constantCoin bit : Val rT).fst #())
      (RealCoin.law (if bit then 1 else 0)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists bit
    cases bit <;>
      isimp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
        Bool.false_eq_true, ite_false, ite_true, (show ((0 : unitInterval) : ℝ) = 0 from rfl),
        (show ((1 : unitInterval) : ℝ) = 1 from rfl), sub_zero, sub_self, ENNReal.ofReal_zero,
        ENNReal.ofReal_one, zero_mul, one_mul, zero_add, add_zero] at Hcredit
    · iframe Hcredit; itrivial
    · iframe Hcredit; itrivial

/-- The heavy-tail endpoint is composed with a concrete always-false callback. -/
example [ProbLangDist.IsUniformInt rT] (E : CoPset) :
    IsDistSpec (GF := GF) E
      pl(&Occil.fractionalPower &(constantCoin false : Val rT).fst #1 #2 #())
      (RealCoin.law (FractionalPower.bias 0 1 2 (by decide) (by decide))) Val.bool :=
  FractionalPower.fractionalPower_distSpec E 0 1 2 (by decide) (by decide)
    (constantCoin false) (constantCoin_spec E false)

/-- The full-success endpoint is composed with a concrete always-true callback. -/
example [ProbLangDist.IsUniformInt rT] (E : CoPset) :
    IsDistSpec (GF := GF) E
      pl(&Occil.fractionalPower &(constantCoin true : Val rT).fst #1 #1 #())
      (RealCoin.law (FractionalPower.bias 1 1 1 (by decide) (by decide))) Val.bool :=
  FractionalPower.fractionalPower_distSpec E 1 1 1 (by decide) (by decide)
    (constantCoin true) (constantCoin_spec E true)

#print axioms FractionalPower.fractionalPower_distSpec
#print axioms framed_fractional_power

#print axioms RationalPowerInteger.rationalPower_integer_distSpec
#print axioms framed_integer_power

end

end SampLib.ExactPowersCallers
