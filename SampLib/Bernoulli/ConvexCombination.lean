import SampLib.Common.FactorySyntax
import SampLib.Common.Laws.WeightedSupport
import Samplers.Bernoulli.Series

/-! # Finite convex combinations of coins

The coefficient weights select a callback. Its success probability is therefore
the weighted average of the callback biases.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ConvexCombination

noncomputable section

section mathematics

open MeasureTheory

/-- The finite mixture of the supplied coin laws. -/
def law (ws : List ℕ) (p : ℕ → unitInterval) : Measure Bool :=
  (WeightedChoice.law ws).bind (fun i => RealCoin.law (p i))

instance (ws : List ℕ) [NeZero ws.sum] (p : ℕ → unitInterval) :
    IsProbabilityMeasure (law ws p) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- Its bias is the normalized weighted sum of component biases. -/
theorem success_probability (ws : List ℕ) (p : ℕ → unitInterval) :
    law ws p {true} =
      WeightedChoice.weightedSum ws (fun i => ENNReal.ofReal (p i : ℝ)) / ws.sum := by
  rw [law, Measure.bind_apply (measurableSet_singleton true)
    (measurable_of_countable _).aemeasurable]
  simpa [RealCoin.law, RealCoin.pmf] using
    WeightedChoice.lintegral_law ws (fun i => ENNReal.ofReal (p i : ℝ))

/-- Impossible list positions are ruled out by infinite credit. -/
def componentCredit (ws : List ℕ) (p : ℕ → unitInterval) (F : Bool → ℝ≥0∞)
    (i : ℕ) : ℝ≥0∞ :=
  if i < ws.length then RealCoin.credit (p i) F else ∞

/-- Conditioning on the selected component preserves the mixture expectation. -/
theorem expectation (ws : List ℕ) (p : ℕ → unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ i, componentCredit ws p F i ∂WeightedChoice.law ws =
      ∫⁻ b, F b ∂law ws p := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [WeightedChoice.ae_lt_length ws] with i hi
  rw [componentCredit, ite_eq_left hi, RealCoin.lintegral_law]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open FactorySyntax

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Select a valid list position and invoke the corresponding verified callback. -/
theorem twp_convexCombination (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (p : ℕ → unitInterval) (coins : List (Val rT)) (hlen : coins.length = ws.length)
    (hcoins : ∀ i : Fin coins.length, IsDistSpec (GF := GF) E
      pl(&(coins.get i).fst #()) (RealCoin.law (p i)) Val.bool) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law ws p) -∗
      tglWp E pl(&Occil.FactoryExtra.convexCombination
        &(listVal (fun n : ℕ => Val.int n) ws).fst &(listVal id coins).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [weightedChoice_openRec, weightedChoice_closeRec, getAt_openRec, getAt_closeRec]
  twp_bind pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n) ws).fst)
  isimp only [← expectation ws p F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E ws).wp
    (componentCredit ws p F) (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  by_cases hi : i < ws.length
  · have hic : i < coins.length := by simpa only [hlen] using hi
    isimp only [componentCredit, ite_eq_left hi] at Hcredit
    twp_pure
    simp only [getAt_openRec]
    twp_bind pl(&Occil.getAt &(listVal id coins).fst #int (i : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_getAt E id coins ⟨i, hic⟩
    iintro %v %hv
    subst v
    twp_pures
    simp only [id_eq]
    isimp only [← RealCoin.lintegral_law] at Hcredit
    iapply (hcoins ⟨i, hic⟩).spec F (measurable_of_countable F) $$ Hcredit
  · isimp only [componentCredit, ite_eq_right hi] at Hcredit
    ihave %hbad := ErrorCredit.valid $$ Hcredit
    exact (not_lt_of_ge le_top hbad).elim

/-- Typed finite coin mixture, including zero weights and endpoint component biases. -/
theorem convexCombination_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (p : ℕ → unitInterval) (coins : List (Val rT)) (hlen : coins.length = ws.length)
    (hcoins : ∀ i : Fin coins.length, IsDistSpec (GF := GF) E
      pl(&(coins.get i).fst #()) (RealCoin.law (p i)) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.convexCombination
      &(listVal (fun n : ℕ => Val.int n) ws).fst &(listVal id coins).fst #())
      (law ws p) Val.bool where
  spec F _ := wand_entails (twp_convexCombination E ws p coins hlen hcoins F)

end specification

end

end SampLib.ConvexCombination
