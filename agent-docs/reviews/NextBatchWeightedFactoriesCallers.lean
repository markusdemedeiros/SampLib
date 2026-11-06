import SampLib.Templates
import SampLib.Samplers.WeightedChoice
import SampLib.Samplers.WeightedRejection
import SampLib.Samplers.BernsteinFactory
import SampLib.Samplers.PLogInverse
import SampLib.Samplers.FairCoin
import Metrology.Iris.LocalBI

open Set ProbLang
open scoped ENNReal

namespace ReviewNextWeightedFactories

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem frame {α : Type} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ I -∗
      tglWp E pl(&Occil.weightedChoice &(listVal (fun n : ℕ => Val.int n) ws).fst)
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ I)) :=
  frame (WeightedChoice.weightedChoice_distSpec E ws) F I

example : WeightedChoice.law [2, 0, 3] {2} = 3 / 5 := by
  norm_num [WeightedChoice.law_singleton]

example : WeightedChoice.law [0, 2, 0] {0} = 0 := by
  norm_num [WeightedChoice.law_singleton]

example : WeightedChoice.law [0, 2, 0] {1} = 1 := by
  norm_num [WeightedChoice.law_singleton]
  exact ENNReal.div_self (by norm_num) (by norm_num)

example : WeightedChoice.law [0, 2, 0] {3} = 0 := by
  norm_num [WeightedChoice.law_singleton]

example : (∫⁻ i, (if i = 1 then 0 else ∞ : ℝ≥0∞)
    ∂WeightedChoice.law [0, 2, 0]) = 0 := by
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]

example : (∫⁻ i, (if i = 1 then ∞ else 0 : ℝ≥0∞)
    ∂WeightedChoice.law [0, 2, 0]) = ∞ := by
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]
  exact ENNReal.top_div_of_ne_top (by norm_num)

example : (∫⁻ i, (if i = 0 then ∞ else 0 : ℝ≥0∞)
    ∂WeightedChoice.law [0, 2, 0]) = 0 := by
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]

#print axioms WeightedChoice.weightedChoice_distSpec
#print axioms WeightedChoice.rank_partition
#print axioms WeightedChoice.law_singleton

private def zeroCoefficient : BernsteinFactory.Coefficient := ⟨(0, 1), by norm_num⟩
private def oneCoefficient : BernsteinFactory.Coefficient := ⟨(1, 1), by norm_num⟩
private def halfCoefficient : BernsteinFactory.Coefficient := ⟨(1, 2), by norm_num⟩

example (p : unitInterval) :
    BernsteinFactory.law p [zeroCoefficient, oneCoefficient] {true} = ENNReal.ofReal p := by
  norm_num [BernsteinFactory.success_probability, Finset.sum_range_succ,
    BernsteinFactory.coefficient, BernsteinFactory.coefficientBias, zeroCoefficient,
    oneCoefficient, RationalCoin.bias]

example (p : unitInterval) :
    BernsteinFactory.law p [halfCoefficient] {true} = 1 / 2 := by
  norm_num [BernsteinFactory.success_probability, BernsteinFactory.coefficient,
    BernsteinFactory.coefficientBias, halfCoefficient, RationalCoin.bias]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂BernsteinFactory.law 1 [zeroCoefficient]) = 0 := by
  rw [BernsteinFactory.law, MeasureTheory.Measure.lintegral_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  simp [Binomial.law, BernsteinFactory.coefficient, BernsteinFactory.coefficientBias,
    zeroCoefficient, RationalCoin.bias, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

example : (PLogInverse.bias 1 (by norm_num) : ℝ) = 0 := by
  norm_num [PLogInverse.bias]

example : (∫⁻ b, (if b then ∞ else 0 : ℝ≥0∞)
    ∂RealCoin.law (PLogInverse.bias 1 (by norm_num))) = 0 := by
  norm_num [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, PLogInverse.bias]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (qs : List BernsteinFactory.Coefficient) [NeZero qs.length]
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂BernsteinFactory.law p qs) ∗ I -∗
      tglWp E pl(&Occil.bernsteinFactory &coin.fst
        &(listVal (BernsteinFactory.encodeCoefficient (rT := rT)) qs).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (BernsteinFactory.bernsteinFactory_distSpec E p coin hcoin qs) F I

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (p : unitInterval)
    (hp : 0 < (p : ℝ)) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (PLogInverse.bias p hp)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.pLogInverse &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) :=
  frame (PLogInverse.pLogInverse_distSpec E p hp coin hcoin) F I

example (E : CoPset) [ProbLangDist.IsUniformInt rT] :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.pLogInverse &Occil.fairCoin #())
      (RealCoin.law (PLogInverse.bias VonNeumann.fairBias
        (by norm_num [VonNeumann.fairBias]))) Val.bool :=
  PLogInverse.pLogInverse_distSpec E VonNeumann.fairBias
    (by norm_num [VonNeumann.fairBias])
    ⟨Occil.fairCoin, .lam (by is_lc), by is_lc⟩ (FairCoin.fairCoin_distSpec E)

#print axioms BernsteinFactory.bernsteinFactory_distSpec
#print axioms BernsteinFactory.success_probability
#print axioms PLogInverse.pLogInverse_distSpec
#print axioms PLogInverse.success_probability

example (E : CoPset) [ProbLangDist.IsUniformInt rT] (ws : List ℕ) (m : ℕ)
    (hs : 0 < ws.sum) (hm : 0 < m) (hbound : ∀ w ∈ ws, w ≤ m)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ I -∗
      tglWp E pl(&Occil.weightedRejection
        &(listVal (fun n : ℕ => Val.int n) ws).fst #int (m : ℤ))
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ I)) :=
  by
    have : NeZero ws.sum := ⟨hs.ne'⟩
    exact frame (WeightedRejection.weightedRejection_distSpec E ws m hs hm hbound) F I

example (E : CoPset) [ProbLangDist.IsUniformInt rT] :
    letI : NeZero ([1, 1] : List ℕ).sum := ⟨by decide⟩
    IsDistSpec (GF := GF) E pl(&Occil.weightedRejection
      &(listVal (fun n : ℕ => Val.int n) [1, 1]).fst #1)
      (WeightedChoice.law [1, 1]) (fun i => Val.int (i : ℤ)) :=
  WeightedRejection.weightedRejection_distSpec E [1, 1] 1
    (by decide) (by decide) (by simp)

example (E : CoPset) [ProbLangDist.IsUniformInt rT] :
    letI : NeZero ([0, 2, 0] : List ℕ).sum := ⟨by decide⟩
    IsDistSpec (GF := GF) E pl(&Occil.weightedRejection
      &(listVal (fun n : ℕ => Val.int n) [0, 2, 0]).fst #3)
      (WeightedChoice.law [0, 2, 0]) (fun i => Val.int (i : ℤ)) :=
  WeightedRejection.weightedRejection_distSpec E [0, 2, 0] 3
    (by decide) (by decide) (by simp)

#print axioms WeightedRejection.weightedRejection_distSpec
#print axioms WeightedRejection.expectation

end

end ReviewNextWeightedFactories
