import SampLib.Samplers.WordReductions
import SampLib.Samplers.SequentialCoins
import SampLib.Samplers.BinomialHalfBits
import SampLib.Samplers.PoissonOne
import SampLib.Distributions.AcceptedProposal
import Metrology.Iris.LocalBI

/-! Independent clients, finite-word laws, and canonical Poisson checks. -/

open Set ProbLang
open scoped ENNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

private theorem two_div_eight : (2 : ℝ≥0∞) / 8 = 1 / 4 := by
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2
  norm_num

example : FiniteImage.law 8 (fun k => k % 5) {2} = (1 : ℝ≥0∞) / 4 := by
  rw [FiniteImage.law_singleton]
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]
  simpa only [one_div] using two_div_eight

example : FiniteImage.law 8 (fun k => k * 5 / 8) {2} = (1 : ℝ≥0∞) / 8 := by
  rw [FiniteImage.law_singleton]
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

example : FiniteImage.law 8 (fun k => k * 5 / 8) {3} = (1 : ℝ≥0∞) / 4 := by
  rw [FiniteImage.law_singleton]
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]
  simpa only [one_div] using two_div_eight

example : FiniteImage.law 4 (fun k => k * 6 / 4) {2} = 0 := by
  rw [FiniteImage.law_singleton]
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

example : (∫⁻ k, (if k = 5 then ∞ else 0 : ℝ≥0∞)
    ∂FiniteImage.law 4 (fun k => k % 6)) = 0 := by
  norm_num [FiniteImage.lintegral_law, Finset.sum_range_succ]

example : (∫⁻ k, (if k = 0 then 0 else ∞ : ℝ≥0∞)
    ∂FiniteImage.law 1 (fun k => k % 1)) = 0 := by
  norm_num [FiniteImage.lintegral_law, Finset.sum_range_succ]

example : WeightedChoice.law [0, 2, 0] {1} = 1 := by
  norm_num [WeightedChoice.law_singleton]
  exact ENNReal.div_self (by norm_num) (by norm_num)

example : (∫⁻ i, (if i = 1 then 0 else ∞ : ℝ≥0∞)
    ∂WeightedChoice.law [0, 2, 0]) = 0 := by
  simp [WeightedChoice.lintegral_law, WeightedChoice.weightedSum]

example : BinomialHalfBits.law 0 = dirac 0 := rfl

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F k ∂BinomialHalfBits.law 2) = (F 0 + F 1 + F 1 + F 2) / 4 := by
  rw [← BinomialHalfBits.expectation]
  have h1 : BinaryDigits.weight 1 = 1 := by simpa using BinaryDigits.weight_odd 0
  have h2 : BinaryDigits.weight 2 = 1 := by simpa [h1] using BinaryDigits.weight_even 1
  have h3 : BinaryDigits.weight 3 = 2 := by simpa [h1] using BinaryDigits.weight_odd 1
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, h1, h2, h3]

example (n : ℕ) : (∫⁻ _k, (∞ : ℝ≥0∞) ∂BinomialHalfBits.law n) = ∞ := by simp

example : (∫⁻ _k : ℕ, (∞ : ℝ≥0∞) ∂ProbabilityTheory.poissonMeasure 1) = ∞ := by simp

example : ProbabilityTheory.poissonMeasure 1 {0} = ENNReal.ofReal (Real.exp (-1)) := by
  rw [ProbabilityTheory.poissonMeasure_singleton]
  norm_num

example (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    AcceptedProposal.mass μ (fun _ => 0) = 0 := by
  simp [AcceptedProposal.mass, AcceptedProposal.weight]

example (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    AcceptedProposal.law μ (fun _ => 1)
      (by simp [AcceptedProposal.mass, AcceptedProposal.weight]) = μ := by
  simp [AcceptedProposal.law, AcceptedProposal.mass, AcceptedProposal.weight]
  rw [show AcceptedProposal.weight (fun _ : ℕ => (1 : unitInterval)) = 1 from by
    funext x
    simp [AcceptedProposal.weight]]
  exact withDensity_one

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


example (E : CoPset) (n bits : ℕ) (hn : 0 < n) [NeZero (2 ^ bits)]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂FiniteImage.law (2 ^ bits) (fun k => k % n)) ∗ I -∗
      tglWp E pl(&Occil.Weighted.moduloReduction #int (n : ℤ) #int (bits : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (WordReductions.moduloReduction_distSpec E n bits hn) F I

example (E : CoPset) (n bits : ℕ) (hn : 0 < n) [NeZero (2 ^ bits)]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂FiniteImage.law (2 ^ bits) (fun k => k * n / 2 ^ bits)) ∗ I -∗
      tglWp E pl(&Occil.Weighted.multiplyShift #int (n : ℤ) #int (bits : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (WordReductions.multiplyShift_distSpec E n bits hn) F I

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedChoice.law ws) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.sequentialCoins
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ I)) :=
  frame (SequentialCoins.sequentialCoins_distSpec E ws) F I

example (E : CoPset) (n : ℕ) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂BinomialHalfBits.law n) ∗ I -∗
      tglWp E pl(&Occil.DiscreteExtra.binomialHalfBits #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (BinomialHalfBits.binomialHalfBits_distSpec E n) F I

example (E : CoPset) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂ProbabilityTheory.poissonMeasure 1) ∗ I -∗
      tglWp E pl(&Occil.poissonOne #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (PoissonOne.poissonOne_distSpec E) F I

#print axioms WordReductions.moduloReduction_distSpec
#print axioms WordReductions.multiplyShift_distSpec
#print axioms FiniteImage.law_singleton
#print axioms SequentialCoins.sequentialCoins_distSpec
#print axioms SequentialCoins.expectation
#print axioms BinomialHalfBits.binomialHalfBits_distSpec
#print axioms BinomialHalfBits.expectation
#print axioms PoissonOne.poissonOne_distSpec
#print axioms PoissonOne.expectation
#print axioms AcceptedProposal.expectation_preservation

end

end ExpansionDiscreteAudit
