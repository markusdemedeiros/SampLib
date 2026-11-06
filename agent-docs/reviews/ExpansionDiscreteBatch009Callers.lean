import SampLib.Discrete.Borel
import SampLib.Weighted.OneillUniform
import SampLib.Discrete.FisherHypergeometric
import Metrology.Iris.LocalBI

/-! Independent branching-process, lazy-threshold and Fisher clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : Borel.law 0 (by norm_num) = dirac 1 := by
  simp [Borel.law]

example (r : ℝ≥0) (hr : r < 1) : Borel.law r hr {0} = 0 := by
  simp [Borel.law]

example (r : ℝ≥0) (hr : r < 1) : Borel.law r hr Set.univ = 1 := measure_univ

example (r : ℝ≥0) : GaltonWatson.truncation r 1 Set.univ =
    ENNReal.ofReal (Real.exp (-(r : ℝ))) := by
  change GaltonWatson.grow r 0 Set.univ = _
  rw [GaltonWatson.grow_mass, lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp [ProbabilityTheory.poissonMeasure_singleton]

example (r : ℝ≥0) (hr : r < 1) :
    (∫⁻ k, (if k = 0 then ∞ else 0 : ℝ≥0∞) ∂Borel.law r hr) = 0 := by
  have he : (fun k : ℕ => if k = 0 then ∞ else 0 : ℕ → ℝ≥0∞) =
      ({0} : Set ℕ).indicator (fun _ => ∞) := by
    funext k
    simp [Set.indicator]
  rw [he, lintegral_indicator_const (measurableSet_singleton _)]
  simp [Borel.law]

example (r : ℝ≥0) (hr : r < 1) : (∫⁻ _k, (∞ : ℝ≥0∞) ∂Borel.law r hr) = ∞ := by
  simp

example (ones zeros a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    FisherHypergeometric.law 0 ones zeros a b = dirac 0 := by
  apply Measure.ext_of_singleton
  intro k
  rw [FisherHypergeometric.law_singleton 0 ones zeros a b k (by omega) ha hb]
  cases k <;> simp [FisherHypergeometric.weight, FisherHypergeometric.table]

example : FisherHypergeometric.law 1 2 1 2 1 {1} = (4 : ℝ≥0∞) / 5 := by
  rw [FisherHypergeometric.law_singleton 1 2 1 2 1 1 (by decide) (by decide) (by decide)]
  norm_num [FisherHypergeometric.weight, FisherHypergeometric.table, List.range_succ]

example : FisherHypergeometric.law 2 0 3 2 1 {0} = 1 := by
  rw [FisherHypergeometric.law_singleton 2 0 3 2 1 0 (by decide) (by decide) (by decide)]
  norm_num [FisherHypergeometric.weight, FisherHypergeometric.table, List.range_succ]
  exact ENNReal.div_self (by norm_num) (by norm_num)

example : FisherHypergeometric.law 2 3 0 2 1 {2} = 1 := by
  rw [FisherHypergeometric.law_singleton 2 3 0 2 1 2 (by decide) (by decide) (by decide)]
  norm_num [FisherHypergeometric.weight, FisherHypergeometric.table, List.range_succ]
  exact ENNReal.div_self (by norm_num) (by norm_num)

example : FisherHypergeometric.law 3 2 1 2 1 {2} = 1 := by
  rw [FisherHypergeometric.law_singleton 3 2 1 2 1 2 (by decide) (by decide) (by decide)]
  norm_num [FisherHypergeometric.weight, FisherHypergeometric.table, List.range_succ, Nat.choose]
  exact ENNReal.div_self (a := 4) (by norm_num) (by norm_num)

example : (∫⁻ k, (if k = 2 then ∞ else 0 : ℝ≥0∞)
    ∂FisherHypergeometric.law 1 2 1 2 1) = 0 := by
  have he : (fun k : ℕ => if k = 2 then ∞ else 0 : ℕ → ℝ≥0∞) =
      ({2} : Set ℕ).indicator (fun _ => ∞) := by
    funext k
    simp [Set.indicator]
  rw [he, lintegral_indicator_const (measurableSet_singleton _),
    FisherHypergeometric.law_singleton 1 2 1 2 1 2 (by decide) (by decide) (by decide)]
  norm_num

example (n ones zeros a b : ℕ) :
    (∫⁻ _k, (∞ : ℝ≥0∞) ∂FisherHypergeometric.law n ones zeros a b) = ∞ := by simp

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


example (E : CoPset) (x y : ℕ) (hxy : x < y) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Borel.law (PoissonRational.rate x y) (Borel.rate_lt_one x y hxy)) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.borel #int (x : ℤ) #int (y : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (Borel.borel_distSpec E x y hxy) F I

example (E : CoPset) (n bits : ℕ) [NeZero n] (hnw : n ≤ 2 ^ bits)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.oneillUniform #int (n : ℤ) #int (bits : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (OneillUniform.oneillUniform_distSpec E n bits hnw) F I

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.oneillUniform #5 #3) (UniformInt.law 5)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  OneillUniform.oneillUniform_distSpec E 5 3 (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.oneillUniform #3 #3) (UniformInt.law 3)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  OneillUniform.oneillUniform_distSpec E 3 3 (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.oneillUniform #3 #4) (UniformInt.law 3)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  OneillUniform.oneillUniform_distSpec E 3 4 (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.oneillUniform #4 #2) (UniformInt.law 4)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  OneillUniform.oneillUniform_distSpec E 4 2 (by decide)

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.WeightedVariants.oneillUniform #1 #0) (UniformInt.law 1)
      (fun k : ℕ => Val.int (k : ℤ)) :=
  OneillUniform.oneillUniform_distSpec E 1 0 (by decide)

example (E : CoPset) (n ones zeros a b : ℕ) (hn : n ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂FisherHypergeometric.law n ones zeros a b) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.fisherHypergeometric #int (n : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (FisherHypergeometric.fisherHypergeometric_distSpec E n ones zeros a b hn ha hb) F I

#print axioms Borel.borel_distSpec
#print axioms Borel.expectation
#print axioms GaltonWatson.branching
#print axioms GaltonWatson.law_mass
#print axioms GaltonWatson.credit_recurrence
#print axioms GaltonWatson.poisson_mean
#print axioms Distributions.lintegral_poisson_pow
#print axioms OneillUniform.oneillUniform_distSpec
#print axioms FisherHypergeometric.fisherHypergeometric_distSpec
#print axioms FisherHypergeometric.law_singleton
#print axioms FisherHypergeometric.total_pos

end

end ExpansionDiscreteAudit
