import SampLib.Common.FactorySyntax
import SampLib.Bernoulli.ProbabilityGeneratingFactory
import SampLib.Discrete.WeightedChoice
import Samplers.Bernoulli.Series

/-! # Finite positive power-series coins

Selecting an exponent with integer coefficient weights gives the normalized
polynomial `sum c_i p^i / sum c_i`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PositivePowerSeries

noncomputable section

section mathematics

open MeasureTheory

/-- The coefficient-weighted mixture of all-successes coins. -/
abbrev law (p : unitInterval) (ws : List ℕ) [NeZero ws.sum] :=
  ProbabilityGeneratingFactory.law (WeightedChoice.law ws) p

/-- The success atom is the normalized finite positive polynomial. -/
theorem success_probability (p : unitInterval) (ws : List ℕ) [NeZero ws.sum] :
    law p ws {true} =
      WeightedChoice.weightedSum ws (fun i => ENNReal.ofReal ((p : ℝ) ^ i)) / ws.sum := by
  rw [law, ProbabilityGeneratingFactory.law,
    Measure.bind_apply (measurableSet_singleton true) (measurable_of_countable _).aemeasurable]
  simpa [IterateCoin.law, IterateCoin.bias, RealCoin.law, RealCoin.pmf] using
    WeightedChoice.lintegral_law ws (fun i => ENNReal.ofReal ((p : ℝ) ^ i))

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

open FactorySyntax

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Select the exponent, then use the verified all-successes specification. -/
theorem twp_positivePowerSeries (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ws : List ℕ) [NeZero ws.sum] (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p ws) -∗
      tglWp E pl(&Occil.FactoryExtra.positivePowerSeries &coin.fst
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [weightedChoice_openRec, weightedChoice_closeRec,
    iterateCoin_openRec, iterateCoin_closeRec]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n) ws).fst)
  isimp only [← ProbabilityGeneratingFactory.expectation_preservation
    (WeightedChoice.law ws) p F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E ws).wp
    (fun n => IterateCoin.credit p n F) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  twp_pure
  simp only [iterateCoin_openRec]
  iapply (IterateCoin.twp_iterateCoin E p coin hcoin n F) $$ Hcredit

/-- Full unit-interval input domain and all nonnegative coefficient lists of positive total. -/
theorem positivePowerSeries_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.positivePowerSeries &coin.fst
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (law p ws) Val.bool where
  spec F _ := wand_entails (twp_positivePowerSeries E p coin hcoin ws F)

end specification

end

end SampLib.PositivePowerSeries
