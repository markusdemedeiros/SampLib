import SampLib.Samplers.LogarithmicSeries
import SampLib.Samplers.Multinomial
import SampLib.Samplers.WeightedWithoutReplacement
import SampLib.Samplers.CumulativeDraw
import SampLib.Samplers.CumulativeChoice
import SampLib.NatCounters
import Metrology.Iris.LocalBI

/-! Independent logarithmic, multinomial, ordered-selection and cumulative-table clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

private theorem multinomial_nil : ([] : List ℕ).multinomial = 1 := rfl

example : LogarithmicSeries.rationalLaw 1 2 (by decide) (by decide) {1} =
    ENNReal.ofReal ((1 / 2 : ℝ) / (-Real.log (1 / 2))) := by
  rw [LogarithmicSeries.law_succ]
  norm_num [LogarithmicSeries.normalizer,
    BinomialBinary.bias_coe 1 2 (by decide) (by decide)]

example (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    LogarithmicSeries.rationalLaw a b ha hab {0} = 0 :=
  LogarithmicSeries.law_zero _ _ _

example (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂LogarithmicSeries.rationalLaw a b ha hab) = ∞ := by simp

example (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    (∫⁻ k, (if k = 0 then ∞ else 0 : ℝ≥0∞)
      ∂LogarithmicSeries.rationalLaw a b ha hab) = 0 := by
  have he : (fun k : ℕ => if k = 0 then ∞ else 0 : ℕ → ℝ≥0∞) =
      ({0} : Set ℕ).indicator (fun _ => ∞) := by funext k; simp [Set.indicator]
  rw [he, lintegral_indicator_const (measurableSet_singleton _),
    LogarithmicSeries.law_zero, mul_zero]

example : Multinomial.law 2 [1, 2] {[1, 1]} = (4 : ℝ≥0∞) / 9 := by
  rw [Multinomial.law_singleton 2 [1, 2] [1, 1] (by decide)]
  have hp : Multinomial.pmf 2 [1, 2] [1, 1] = (4 : ℝ≥0) / 9 := by
    norm_num [Multinomial.pmf, Multinomial.weightProduct, List.multinomial_cons, multinomial_nil]
  rw [hp, ENNReal.coe_div (by norm_num)]
  norm_num

example : Multinomial.law 2 [1, 2] {[2, 0]} = (1 : ℝ≥0∞) / 9 := by
  rw [Multinomial.law_singleton 2 [1, 2] [2, 0] (by decide)]
  have hp : Multinomial.pmf 2 [1, 2] [2, 0] = (1 : ℝ≥0) / 9 := by
    norm_num [Multinomial.pmf, Multinomial.weightProduct, List.multinomial_cons, multinomial_nil]
  rw [hp, ENNReal.coe_div (by norm_num)]
  norm_num

example : Multinomial.law 2 [0, 3, 0] {[1, 1, 0]} = 0 := by
  rw [Multinomial.law_singleton 2 [0, 3, 0] [1, 1, 0] (by decide)]
  norm_num [Multinomial.pmf, Multinomial.weightProduct, List.multinomial_cons]

example : Multinomial.law 2 [1, 2] {[2]} = 0 := by
  rw [Multinomial.law_singleton 2 [1, 2] [2] (by decide)]
  norm_num [Multinomial.pmf]

example : Multinomial.law 2 [1, 2] {[1, 0]} = 0 := by
  rw [Multinomial.law_singleton 2 [1, 2] [1, 0] (by decide)]
  norm_num [Multinomial.pmf]

example : Multinomial.law 0 [0, 0] = dirac [0, 0] := by simp
example : Multinomial.law 0 [] = dirac [] := by simp

example (n : ℕ) (ws : List ℕ) : (∫⁻ _cs, (∞ : ℝ≥0∞) ∂Multinomial.law n ws) = ∞ := by
  simp

example : WeightedSelections.law [0, 0] 0 = dirac [] := rfl
example : WeightedSelections.law [] 0 = dirac [] := rfl

example : WeightedSelections.law [2, 1] 2 {[0, 1]} = (2 : ℝ≥0∞) / 3 := by
  rw [WeightedSelections.law_singleton _ _ (by decide)]
  norm_num [WeightedSelections.likelihood]

example : WeightedSelections.law [2, 1] 2 {[1, 0]} = (1 : ℝ≥0∞) / 3 := by
  rw [WeightedSelections.law_singleton _ _ (by decide)]
  norm_num [WeightedSelections.likelihood]
  rw [ENNReal.div_self (a := 2) (by norm_num) (by norm_num), mul_one]

example : WeightedSelections.law [2, 1] 2 {[0, 0]} = 0 := by
  rw [WeightedSelections.law_singleton _ _ (by decide)]
  norm_num [WeightedSelections.likelihood]

example : WeightedSelections.law [2, 1] 2 {[0]} = 0 := by
  rw [WeightedSelections.law_singleton _ _ (by decide)]
  norm_num

example : WeightedSelections.law [0, 3, 0] 1 {[1]} = 1 := by
  rw [WeightedSelections.law_singleton _ _ (by decide)]
  norm_num [WeightedSelections.likelihood]
  exact ENNReal.div_self (a := 3) (by norm_num) (by norm_num)

example : (∫⁻ is, (if is = [0, 0] then ∞ else 0 : ℝ≥0∞)
    ∂WeightedSelections.law [2, 1] 2) = 0 := by
  have he : (fun is : List ℕ => if is = [0, 0] then ∞ else 0 : List ℕ → ℝ≥0∞) =
      ({[0, 0]} : Set (List ℕ)).indicator (fun _ => ∞) := by
    funext is
    simp [Set.indicator]
  rw [he, lintegral_indicator_const (measurableSet_singleton _),
    WeightedSelections.law_singleton _ _ (by decide)]
  norm_num [WeightedSelections.likelihood]

private def plateauCDF : FiniteCDF.Model where
  lower := 0
  upper := 3
  nonempty := by decide
  scale := 5
  positive := by decide
  cdf := fun x => if x < 1 then 0 else if x < 3 then 2 else 5
  monotone := by intro x hx y hy hxy; dsimp; split_ifs <;> omega
  bounded := by intro x hx; dsimp; split_ifs <;> omega
  upper_mass := rfl

private def lowerAtomCDF : FiniteCDF.Model where
  lower := 0
  upper := 2
  nonempty := by decide
  scale := 5
  positive := by decide
  cdf := fun x => if x < 2 then 2 else 5
  monotone := by intro x hx y hy hxy; dsimp; split_ifs <;> omega
  bounded := by intro x hx; dsimp; split_ifs <;> omega
  upper_mass := rfl

private def singletonCDF : FiniteCDF.Model where
  lower := 0
  upper := 0
  nonempty := by decide
  scale := 1
  positive := by decide
  cdf := fun _ => 1
  monotone := by intro x hx y hy hxy; exact le_rfl
  bounded := by intro x hx; norm_num
  upper_mass := rfl

example : FiniteCDF.law plateauCDF (Set.Iic 1) = ENNReal.ofReal (2 / 5 : ℝ) := by
  simpa [plateauCDF] using FiniteCDF.cdf plateauCDF 1 (by norm_num [plateauCDF])

example : FiniteCDF.law plateauCDF (Set.Iic 2) = ENNReal.ofReal (2 / 5 : ℝ) := by
  simpa [plateauCDF] using FiniteCDF.cdf plateauCDF 2 (by norm_num [plateauCDF])

example : FiniteCDF.law lowerAtomCDF (Set.Iic 0) = ENNReal.ofReal (2 / 5 : ℝ) := by
  simpa [lowerAtomCDF] using FiniteCDF.cdf lowerAtomCDF 0 (by norm_num [lowerAtomCDF])

example (i : Fin 1) : FiniteCDF.quantile singletonCDF i = 0 := by
  have h := (FiniteCDF.quantile_mem singletonCDF i).1
  norm_num [singletonCDF] at h
  omega

example (D : FiniteCDF.Model) : (∫⁻ _k, (∞ : ℝ≥0∞) ∂FiniteCDF.law D) = ∞ := by simp

example : CategoricalCDF.scan [0, 2, 0, 3] 0 = [0, 2, 2, 5] := by decide

example : CategoricalCDF.law [0, 2, 0, 3] {1} = (2 : ℝ≥0∞) / 5 := by
  rw [← lintegral_indicator_one (measurableSet_singleton (1 : ℤ)), CategoricalCDF.law,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, Set.indicator]

example : CategoricalCDF.law [0, 2, 0, 3] {3} = (3 : ℝ≥0∞) / 5 := by
  rw [← lintegral_indicator_one (measurableSet_singleton (3 : ℤ)), CategoricalCDF.law,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum, Set.indicator]

example : (∫⁻ z, (if z = 0 then ∞ else 0 : ℝ≥0∞)
    ∂CategoricalCDF.law [0, 2, 0, 3]) = 0 := by
  rw [CategoricalCDF.law,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    WeightedChoice.lintegral_law]
  norm_num [WeightedChoice.weightedSum]

example (F : ℤ → ℝ≥0∞) : (∫⁻ z, F z ∂CategoricalCDF.law [7]) = F 0 := by
  rw [CategoricalCDF.law,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    WeightedChoice.lintegral_law]
  simp only [WeightedChoice.weightedSum, List.sum_cons, List.sum_nil, add_zero,
    Nat.cast_ofNat, Nat.cast_zero]
  rw [mul_comm (7 : ℝ≥0∞), ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem frame {α : Type} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
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


example (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂LogarithmicSeries.rationalLaw a b ha hab) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.logarithmicSeries #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (LogarithmicSeries.logarithmicSeries_distSpec E a b ha hab) F I

example (E : CoPset) (n : ℕ) (ws : List ℕ) (hvalid : n = 0 ∨ 0 < ws.sum)
    (F : List ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ cs, F cs ∂Multinomial.law n ws) ∗ I -∗
      tglWp E pl(&Occil.multinomial #int (n : ℤ)
        &(listVal (fun k : ℕ => Val.int (k : ℤ)) ws).fst)
        (fun v : Val rT => iprop(∃ cs : List ℕ,
          ⌜v = listVal (fun k : ℕ => Val.int (k : ℤ)) cs⌝ ∗ ↯ (F cs) ∗ I)) :=
  frame (Multinomial.multinomial_distSpec E n ws hvalid) F I

example (E : CoPset) (ws : List ℕ) (k : ℕ) (hk : k ≤ WeightedSelections.positiveCount ws)
    (F : List ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ is, F is ∂WeightedSelections.law ws k) ∗ I -∗
      tglWp E pl(&Occil.weightedWithoutReplacement
        &(listVal (fun i : ℕ => Val.int i) ws).fst #int (k : ℤ))
        (fun v : Val rT => iprop(∃ is : List ℕ,
          ⌜v = listVal (fun i : ℕ => Val.int i) is⌝ ∗ ↯ (F is) ∗ I)) :=
  frame (WeightedWithoutReplacement.weightedWithoutReplacement_distSpec E ws k hk) F I

example (E : CoPset) (D : FiniteCDF.Model) (n : ℕ) (hl : D.lower = 0)
    (hu : D.upper = (n : ℤ) - 1) (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂FiniteCDF.law D) ∗ I -∗
      tglWp E pl(&Occil.Weighted.cumulativeDraw &(CumulativeDraw.table D n).fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ I)) :=
  frame (CumulativeDraw.cumulativeDraw_distSpec E D n hl hu) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.cumulativeDraw &(CumulativeDraw.table plateauCDF 4).fst #())
      (FiniteCDF.law plateauCDF) Val.int :=
  CumulativeDraw.cumulativeDraw_distSpec E plateauCDF 4 rfl rfl

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.cumulativeDraw &(CumulativeDraw.table lowerAtomCDF 3).fst #())
      (FiniteCDF.law lowerAtomCDF) Val.int :=
  CumulativeDraw.cumulativeDraw_distSpec E lowerAtomCDF 3 rfl rfl

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.cumulativeDraw &(CumulativeDraw.table singletonCDF 1).fst #())
      (FiniteCDF.law singletonCDF) Val.int :=
  CumulativeDraw.cumulativeDraw_distSpec E singletonCDF 1 rfl rfl

#print axioms LogarithmicSeries.logarithmicSeries_distSpec
#print axioms LogarithmicSeries.expectation_preservation
#print axioms LogarithmicSeries.mass_eq
#print axioms LogarithmicSeries.law_succ
#print axioms Multinomial.multinomial_distSpec
#print axioms Multinomial.law_singleton
#print axioms Multinomial.tsum_pmf
#print axioms Multinomial.expectation
#print axioms WeightedWithoutReplacement.weightedWithoutReplacement_distSpec
#print axioms WeightedSelections.law_singleton
#print axioms WeightedSelections.support
#print axioms CumulativeDraw.cumulativeDraw_distSpec
#print axioms CumulativeDraw.twp_search
#print axioms FiniteCDF.cdf

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂CategoricalCDF.law ws) ∗ I -∗
      tglWp E pl(&Occil.Weighted.cumulativeChoice
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z) ∗ I)) :=
  frame (CumulativeChoice.cumulativeChoice_distSpec E ws) F I

omit [ProbLangDist.IsUniformInt rT] in
private theorem pure_frame {E : CoPset} {e : Exp rT} {value : Val rT}
    (h : ⊢ tglWp E e (fun v => iprop(⌜v = value⌝))) (I : IProp GF) :
    ⊢ I -∗ tglWp E e (fun v => iprop(⌜v = value⌝ ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply h
  iintro %v %hv
  iframe HI
  itrivial

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (n : ℕ) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.DiscreteExtra.zeroCounters #int (n : ℤ))
      (fun v => iprop(⌜v = NatCounters.encode (List.replicate n 0)⌝ ∗ I)) :=
  pure_frame (NatCounters.twp_zeroCounters E n) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (xs : List ℕ) (i : ℕ) (hi : i < xs.length) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.DiscreteExtra.incrementCounter
      &(NatCounters.encode xs).fst #int (i : ℤ))
      (fun v => iprop(⌜v = NatCounters.encode (xs.modify i (· + 1))⌝ ∗ I)) :=
  pure_frame (NatCounters.twp_incrementCounter E xs i hi) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (xs : List ℕ) (i : ℕ) (hi : i < xs.length)
    (hpos : 0 < xs[i]) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.DiscreteExtra.adjustCounter
      &(NatCounters.encode xs).fst #int (i : ℤ) #int (-1 : ℤ))
      (fun v => iprop(⌜v = NatCounters.encode (xs.modify i (· - 1))⌝ ∗ I)) :=
  pure_frame (NatCounters.twp_decrementCounter E xs i hi hpos) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.adjustCounter
      &(NatCounters.encode [2, 1, 3]).fst #1 #int (-1 : ℤ))
      (fun v => iprop(⌜v = NatCounters.encode [2, 0, 3]⌝)) := by
  simpa using NatCounters.twp_decrementCounter (rT := rT) (GF := GF)
    E [2, 1, 3] 1 (by decide) (by decide)

#print axioms CumulativeChoice.cumulativeChoice_distSpec
#print axioms CategoricalCDF.quantile_category
#print axioms CategoricalCDF.law_eq
#print axioms CategoricalCDF.scan_eq_cumulative
#print axioms NatCounters.twp_zeroCounters
#print axioms NatCounters.twp_incrementCounter
#print axioms NatCounters.twp_decrementCounter

end

end ExpansionDiscreteAudit
