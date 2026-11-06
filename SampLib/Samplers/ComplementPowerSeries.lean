import SampLib.FactorySyntax
import SampLib.CoinComplement
import Samplers.Bernoulli.Series

/-! # Complementary positive power-series coins

The coefficient-weighted success probability is
`1 - sum c_i (1-p)^(i+1) / sum c_i`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ComplementPowerSeries

noncomputable section

/-- The selected exponent requires at least one failure of the complemented input. -/
def componentBias (p : unitInterval) (n : ℕ) : unitInterval :=
  unitInterval.symm (IterateCoin.bias (unitInterval.symm p) (n + 1))

section mathematics

open MeasureTheory

/-- The coefficient-weighted mixture of complementary all-successes laws. -/
def law (p : unitInterval) (ws : List ℕ) : Measure Bool :=
  (WeightedChoice.law ws).bind (fun n => RealCoin.law (componentBias p n))

instance (p : unitInterval) (ws : List ℕ) [NeZero ws.sum] :
    IsProbabilityMeasure (law p ws) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- The success atom is the complementary polynomial, including endpoint biases. -/
theorem success_probability (p : unitInterval) (ws : List ℕ) :
    law p ws {true} = WeightedChoice.weightedSum ws
      (fun n => ENNReal.ofReal (1 - (1 - (p : ℝ)) ^ (n + 1))) / ws.sum := by
  rw [law, Measure.bind_apply (measurableSet_singleton true)
    (measurable_of_countable _).aemeasurable]
  simpa [RealCoin.law, RealCoin.pmf, componentBias, IterateCoin.bias,
    unitInterval.coe_symm_eq] using WeightedChoice.lintegral_law ws
      (fun n => ENNReal.ofReal (1 - (1 - (p : ℝ)) ^ (n + 1)))

/-- Credit before the selected run of complemented flips. -/
def continuation (p : unitInterval) (F : Bool → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  IterateCoin.credit (unitInterval.symm p) (n + 1) (fun b => F (!b))

/-- Conditioning on the exponent and complementing the run preserves expectation. -/
theorem expectation (p : unitInterval) (ws : List ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ n, continuation p F n ∂WeightedChoice.law ws = ∫⁻ b, F b ∂law p ws := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  apply lintegral_congr
  intro n
  simpa only [continuation, IterateCoin.credit, ← RealCoin.lintegral_law,
    componentBias, Complement.law] using
    Complement.expectation_preservation (IterateCoin.bias (unitInterval.symm p) (n + 1)) F

end mathematics

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

section specification

open FactorySyntax
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Select the exponent, run complemented flips, then negate their conjunction. -/
theorem twp_complementPowerSeries (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ws : List ℕ) [NeZero ws.sum] (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p ws) -∗
      tglWp E pl(&Occil.FactoryExtra.complementPowerSeries &coin.fst
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [weightedChoice_openRec, weightedChoice_closeRec,
    iterateCoin_openRec, iterateCoin_closeRec]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n) ws).fst)
  isimp only [← expectation p ws F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E ws).wp
    (continuation p F) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 2 twp_pure
  simp only [iterateCoin_openRec]
  rw [← Nat.cast_add_one]
  twp_bind pl(&Occil.iterateCoin &(CoinComplement.callback coin).fst #int ((n + 1 : ℕ) : ℤ))
  isimp only [continuation, IterateCoin.credit, ← RealCoin.lintegral_law] at Hcredit
  iapply ((IterateCoin.iterateCoin_distSpec E (unitInterval.symm p)
    (CoinComplement.callback coin) (CoinComplement.distSpec E p coin hcoin) (n + 1)).wp
    (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  twp_value
  imodintro
  iexists !b
  iframe Hcredit
  ipureintro
  simp only [Val.ext_iff, bool_not]

/-- Full input-bias domain, with nonnegative coefficients of positive total. -/
theorem complementPowerSeries_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementPowerSeries &coin.fst
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (law p ws) Val.bool where
  spec F _ := wand_entails (twp_complementPowerSeries E p coin hcoin ws F)

end specification

end

end SampLib.ComplementPowerSeries
