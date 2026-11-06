import SampLib.Distributions.BinomialShiftPower
import SampLib.Distributions.ShiftedExponential
import SampLib.FactoryChoose
import SampLib.FactoryIntegerPower
import SampLib.FactorySyntax
import SampLib.Samplers.IterateCoin
import SampLib.Samplers.CoinProduct

/-! # The finite binomial-product loop of the shifted-power factory

The exponential operation is a supplied verified function in this loop lemma.
The concrete sampler theorem instantiates it with the actual martingale factory.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ShiftPowerCore

noncomputable section

/-- An ignored unit argument keeps the original callback's free variables intact. -/
def powerCoin {rT : Type} (coin : Val rT) (i : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.iterateCoin &coin.fst #int (i : ℤ)), .lam (by is_lc), by is_lc⟩

private def exponentialCoin {rT : Type} (coin exponential : Val rT) (i : ℕ) : Val rT :=
  ⟨.lam pl(&exponential.fst &(powerCoin coin i).fst #()), .lam (by is_lc), by is_lc⟩

/-- The source loop with only its exponential function parameterized. -/
def loop {rT : Type} (coin exponential : Val rT) (m k : ℕ) : Exp rT :=
  let power := .lam pl(&Occil.iterateCoin &coin.fst &(.bvar 3))
  let trial := pl(&Occil.iterateCoin &(.lam pl(&exponential.fst &power #())) &(.bvar 0))
  let repetitions := pl(&Occil.FactoryExtra.choose #int (k : ℤ) &(.bvar 0) *
    &Occil.FactoryExtra.intPower #int (m : ℤ) (#int (k : ℤ) - &(.bvar 0)))
  let again := pl(&(.bvar 2) (&(.bvar 1) + #1))
  .fix (.lam (.cond pl(#int (k : ℤ) < &(.bvar 0)) pl(#true)
    (.app (.lam (.cond trial again pl(#false))) repetitions)))

private theorem repeated_bias (p : unitInterval) (m k i : ℕ) :
    IterateCoin.bias (ShiftedExponential.unitBias (IterateCoin.bias p i))
      (BinomialShiftPower.coefficient m k i) = BinomialShiftPower.factorBias p m k i := by
  apply Subtype.ext
  exact BinomialShiftPower.factor_power p m k i

/-- Each factor removes exactly its binomial monomial from the remaining exponent. -/
theorem expectation (p : unitInterval) (m k i : ℕ) (hi : i ≤ k) (F : Bool → ℝ≥0∞) :
    (∫⁻ b, CoinProduct.firstCredit (BinomialShiftPower.tailBias p m k (i + 1)) F b
      ∂RealCoin.law (IterateCoin.bias
        (ShiftedExponential.unitBias (IterateCoin.bias p i))
        (BinomialShiftPower.coefficient m k i))) =
      ∫⁻ b, F b ∂RealCoin.law (BinomialShiftPower.tailBias p m k i) := by
  rw [CoinProduct.expectation_preservation, CoinProduct.law, repeated_bias,
    ← BinomialShiftPower.tail_step p m k i hi]

private theorem done_credit (p : unitInterval) (m k i : ℕ) (hi : k < i)
    (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂RealCoin.law (BinomialShiftPower.tailBias p m k i)) = F true := by
  rw [BinomialShiftPower.tail_done p m k i hi]
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

private theorem done_guard (k : ℕ) : decide ((k : ℤ) < ((k + 1 : ℕ) : ℤ)) = true := by simp

private theorem index_le (i k steps : ℕ) (h : i + (steps + 1) = k + 1) : i ≤ k := by
  omega

private theorem continue_guard (i k steps : ℕ) (h : i + (steps + 1) = k + 1) :
    decide ((k : ℤ) < (i : ℤ)) = false := decide_eq_false (by omega)

theorem intPower_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.intPower = Occil.FactoryExtra.intPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem intPower_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.intPower : Exp rT) = Occil.FactoryExtra.intPower :=
  Exp.closeRec_fresh x _ k (by simp [Occil.FactoryExtra.intPower, Exp.fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Finite input-coin iteration supplies the inner p^i callback. -/
theorem powerCoin_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (i : ℕ) :
    IsDistSpec (GF := GF) E pl(&(powerCoin coin i).fst #())
      (RealCoin.law (IterateCoin.bias p i)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [FactorySyntax.iterateCoin_openRec]
    iapply (IterateCoin.iterateCoin_distSpec E p coin hcoin i).spec F hF $$ Hcredit

private theorem exponentialCoin_spec (E : CoPset) (p : unitInterval) (coin exponential : Val rT)
    (hsampler : ∀ i : ℕ, IsDistSpec (GF := GF) E
      pl(&exponential.fst &(powerCoin coin i).fst #())
      (RealCoin.law (ShiftedExponential.unitBias (IterateCoin.bias p i))) Val.bool) (i : ℕ) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin coin exponential i).fst #())
      (RealCoin.law (ShiftedExponential.unitBias (IterateCoin.bias p i))) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (hsampler i).spec F hF $$ Hcredit

/-- Finite induction supplies total correctness for every loop index up to k+1. -/
theorem twp_loop (E : CoPset) (p : unitInterval) (coin exponential : Val rT)
    (hsampler : ∀ i : ℕ, IsDistSpec (GF := GF) E
      pl(&exponential.fst &(powerCoin coin i).fst #())
      (RealCoin.law (ShiftedExponential.unitBias (IterateCoin.bias p i))) Val.bool)
    (m k i steps : ℕ) (hi : i + steps = k + 1) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (BinomialShiftPower.tailBias p m k i)) -∗
      tglWp E pl(&(loop coin exponential m k) #int (i : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction steps generalizing i with
  | zero =>
    have he : i = k + 1 := by simpa using hi
    subst i
    iintro Hcredit
    twp_pures
    rw [done_guard]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [done_credit p m k (k + 1) (Nat.lt_succ_self _) F] at Hcredit
    iframe Hcredit
    itrivial
  | succ steps IH =>
    have hik := index_le i k steps hi
    iintro Hcredit
    twp_pures
    rw [continue_guard i k steps hi]
    twp_pure
    twp_pure
    rw [← Nat.cast_sub hik]
    isimp only [intPower_openRec, intPower_closeRec, FactoryChoose.choose_openRec,
      FactoryChoose.choose_closeRec, FactorySyntax.iterateCoin_openRec,
      FactorySyntax.iterateCoin_closeRec]
    twp_bind pl(&Occil.FactoryExtra.intPower #int (m : ℤ) #int ((k - i : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply FactoryIntegerPower.twp_intPower E (m : ℤ) (k - i)
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.FactoryExtra.choose #int (k : ℤ) #int (i : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply FactoryChoose.twp_choose E k i
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    rw [← Nat.cast_pow, ← Nat.cast_mul]
    twp_bind pl(&Occil.iterateCoin &(exponentialCoin coin exponential i).fst
      #int (BinomialShiftPower.coefficient m k i : ℤ))
    isimp only [← expectation p m k i hik F] at Hcredit
    iapply ((IterateCoin.iterateCoin_distSpec E
      (ShiftedExponential.unitBias (IterateCoin.bias p i)) (exponentialCoin coin exponential i)
      (exponentialCoin_spec E p coin exponential hsampler i)
      (BinomialShiftPower.coefficient m k i)).wp
      (CoinProduct.firstCredit (BinomialShiftPower.tailBias p m k (i + 1)) F)
      (measurable_of_finite _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      rw [← Nat.cast_add_one]
      have hnext := IH (i + 1)
        (by simpa only [Nat.add_assoc, Nat.add_comm 1 steps] using hi)
      simp only [loop] at hnext
      isimp only [FactorySyntax.iterateCoin_openRec, intPower_openRec,
        FactoryChoose.choose_openRec, Exp.ofVal]
      iapply hnext $$ Hcredit

end specification

end

end SampLib.ShiftPowerCore
