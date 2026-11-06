import SampLib.Bernoulli.CoinProduct
import SampLib.Uniform.RationalCoin

/-! # Fresh thinned coins for unknown-rate lazy exponentials -/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNDecayCoins

noncomputable section

/-- Conditional thinning by one uniform integer rank. -/
def callback {rT : Type _} (coin : Val rT) (divisor : ℕ) : Val rT :=
  ⟨.lam pl(if &coin.fst #() then &Occil.rationalCoin #1 #int (divisor : ℤ) else #false),
    .lam (by is_lc), by is_lc⟩

/-- The known thinning probability `1/divisor`. -/
def thinning (divisor : ℕ) (hd : 0 < divisor) : unitInterval :=
  RationalCoin.bias 1 divisor (by omega) (by exact_mod_cast hd) (by exact_mod_cast hd)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Each use flips the unknown input coin afresh, then independently keeps one
of `divisor` uniform ranks. No probability parameter is exposed to the program. -/
theorem distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (divisor : ℕ) (hd : 0 < divisor) :
    IsDistSpec (GF := GF) E pl(&(callback coin divisor).fst #())
      (RealCoin.law (p * thinning divisor hd)) Val.bool where
  spec F _ := by
    have hthin : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #1 #int (divisor : ℤ))
        (RealCoin.law (thinning divisor hd)) Val.bool :=
      RationalCoin.rationalCoin_distSpec E 1 divisor (by omega)
        (by exact_mod_cast hd) (by exact_mod_cast hd)
    iintro Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    twp_bind pl(&coin.fst #())
    isimp only [← CoinProduct.expectation_preservation p (thinning divisor hd) F] at Hcredit
    iapply (hcoin.wp (CoinProduct.firstCredit (thinning divisor hd) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %bit Hcredit
    cases bit
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      iapply hthin.spec F (measurable_of_countable _) $$ Hcredit

end specification

end

end SampLib.PSRNDecayCoins
