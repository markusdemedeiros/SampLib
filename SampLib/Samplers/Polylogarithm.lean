import SampLib.CoinComplement
import SampLib.FactoryIntegerPower
import SampLib.Samplers.Geometric
import SampLib.Samplers.RationalCoin
import Samplers.Bernoulli.Elementary

/-! # Polylogarithmic coins

A geometric count selects a reciprocal integer power. The success probability is
`(1-p) sum p^n/(n+1)^order`, the normalized polylogarithmic series, extended to one
at `p=0`.
-/

open ProbLang
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.Polylogarithm

noncomputable section

private theorem denominator_pos (order n : ℕ) : 0 < (n + 1 : ℤ) ^ order := by
  positivity

private theorem denominator_ge_one (order n : ℕ) : 1 ≤ (n + 1 : ℤ) ^ order :=
  one_le_pow₀ (by omega)

/-- Reciprocal integer powers are valid rational probabilities. -/
def componentBias (order n : ℕ) : unitInterval :=
  RationalCoin.bias 1 ((n + 1 : ℤ) ^ order) zero_le_one (denominator_pos order n)
    (denominator_ge_one order n)

section mathematics

open MeasureTheory ProbabilityTheory

/-- Geometric mixture of reciprocal-power coins. -/
def law (p : unitInterval) (order : ℕ) : Measure Bool :=
  (Geometric.law (unitInterval.symm p)).bind (fun n => RealCoin.law (componentBias order n))

instance (p : unitInterval) (order : ℕ) : IsProbabilityMeasure (law p order) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- The reciprocal-power mixture is the normalized polylogarithmic power series. -/
theorem success_probability (p : unitInterval) (hp : (p : ℝ) < 1) (order : ℕ) :
    law p order {true} = ofReal (1 - (p : ℝ)) *
      ∑' n : ℕ, ofReal ((p : ℝ) ^ n / (n + 1 : ℝ) ^ order) := by
  have hq : unitInterval.symm p ≠ 0 := by
    intro h
    have : (unitInterval.symm p : ℝ) = 0 := by rw [h]; rfl
    rw [unitInterval.coe_symm_eq] at this
    linarith
  rw [law, Measure.bind_apply (measurableSet_singleton true)
    (measurable_of_countable _).aemeasurable, Geometric.law,
    geometricMeasure_eq hq, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  have hcomponent : RealCoin.law (componentBias order n) {true} =
      ofReal (1 / (n + 1 : ℝ) ^ order) := by
    simp [componentBias, RationalCoin.bias, RealCoin.law, RealCoin.pmf]
  rw [hcomponent, ← ENNReal.ofReal_mul (geometricMeasure_nonneg (unitInterval.symm p) n),
    ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]
  congr 1
  simp only [unitInterval.coe_symm_eq]
  ring

/-- Conditional expected credit after observing the geometric count. -/
def continuation (order : ℕ) (F : Bool → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  RealCoin.credit (componentBias order n) F

/-- Conditioning on the count gives the full Boolean expectation, including infinite credits. -/
theorem expectation (p : unitInterval) (order : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ n, continuation order F n ∂Geometric.law (unitInterval.symm p) =
      ∫⁻ b, F b ∂law p order := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  simp only [continuation, RealCoin.lintegral_law]

end mathematics

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem power_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.intPower = Occil.FactoryExtra.intPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem power_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.intPower : Exp rT) = Occil.FactoryExtra.intPower :=
  Exp.closeRec_fresh x _ k (by simp [Occil.FactoryExtra.intPower, Exp.fv])

private theorem complement_pos (p : unitInterval) (hp : (p : ℝ) < 1) :
    0 < (unitInterval.symm p : ℝ) := by
  simpa only [unitInterval.coe_symm_eq] using sub_pos.mpr hp

private theorem order_test (order : ℕ) (horder : 0 < order) :
    decide ((order : ℤ) ≤ 0) = false := by
  exact decide_eq_false (by exact_mod_cast Nat.not_le.mpr horder)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Draw the geometric count, compute its power, then use the exact rational coin. -/
theorem twp_polylogarithm (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (order : ℕ) (horder : 0 < order) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p order) -∗
      tglWp E pl(&Occil.FactoryExtra.polylogarithm &coin.fst #int (order : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_pures
  rw [order_test order horder]
  twp_pure
  simp only [geometric_open, geometric_close, power_open, power_close,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.geometric &(CoinComplement.callback coin).fst #())
  isimp only [← expectation p order F] at Hcredit
  iapply ((Geometric.geometric_distSpec E (unitInterval.symm p) (complement_pos p hp)
    (CoinComplement.callback coin) (CoinComplement.distSpec E p coin hcoin)).wp
    (continuation order F) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 2 twp_pure
  simp only [power_open, RationalCoin.rationalCoin_openRec]
  rw [← Nat.cast_add_one]
  twp_bind pl(&Occil.FactoryExtra.intPower #int ((n + 1 : ℕ) : ℤ) #int (order : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower
  iintro %v %hv
  subst v
  simp only [Nat.cast_add_one, Exp.ofVal]
  isimp only [continuation, componentBias] at Hcredit
  iapply (RationalCoin.twp_rationalCoin E 1 ((n + 1 : ℤ) ^ order)
    zero_le_one (denominator_pos order n) (denominator_ge_one order n) F) $$ Hcredit

/-- Every positive integer order and every terminating bias `p<1`, including zero. -/
theorem polylogarithm_distSpec (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (order : ℕ) (horder : 0 < order) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.polylogarithm
      &coin.fst #int (order : ℤ) #()) (law p order) Val.bool where
  spec F _ := wand_entails (twp_polylogarithm E p hp order horder coin hcoin F)

end specification

end

end SampLib.Polylogarithm
