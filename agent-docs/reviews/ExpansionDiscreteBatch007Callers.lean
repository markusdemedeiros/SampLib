import SampLib.Weighted.WeightedReservoirOne
import SampLib.Weighted.DivisionRejection
import SampLib.Weighted.DebiasedModulo
import Metrology.Iris.LocalBI

/-! Independent weighted-reservoir and finite-word rejection clients. -/

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : (∫⁻ i, (if i = (-1 : ℤ) then ∞ else 0 : ℝ≥0∞)
    ∂WeightedReservoirOne.law [0, 2, 0]) = 0 := by
  simp [WeightedReservoirOne.lintegral_law, WeightedChoice.weightedSum]

example (F : ℤ → ℝ≥0∞) :
    (∫⁻ i, F i ∂WeightedReservoirOne.law [0, 2, 0]) = F 1 := by
  rw [WeightedReservoirOne.lintegral_law]
  simp only [WeightedChoice.weightedSum, List.sum_cons, List.sum_nil,
    Nat.cast_zero, Nat.cast_ofNat, zero_mul, zero_add, add_zero]
  rw [mul_comm (2 : ℝ≥0∞), ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]
  norm_num

example (F : ℤ → ℝ≥0∞) :
    WeightedReservoirOne.credit 0 (-1) [0, 1] 0 F = F 1 := by
  rw [WeightedReservoirOne.initial_credit, WeightedReservoirOne.lintegral_law]
  simp [WeightedChoice.weightedSum]

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F (k / 2) ∂UniformInt.law 6) = ∫⁻ k, F k ∂UniformInt.law 3 := by
  simpa using WordIntervals.quotient_expectation 2 3 (by decide) F

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ k, F (k % 3) ∂UniformInt.law 6) = ∫⁻ k, F k ∂UniformInt.law 3 := by
  simpa using WordIntervals.remainder_expectation 3 2 (by decide) F

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    DivisionRejection.kernel 3 4 F ε 3 = (∫⁻ k, F k ∂UniformInt.law 3) + 2 * ε := by
  norm_num [DivisionRejection.kernel]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, DivisionRejection.kernel 5 8 F ε k ∂UniformInt.law 8) =
      ((∑ k ∈ Finset.range 5, F k) + 3 * ((∫⁻ k, F k ∂UniformInt.law 5) + 2 * ε)) / 8 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, DivisionRejection.kernel]
  simp only [ENNReal.div_eq_inv_mul]
  ring

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, DivisionRejection.kernel 1 1 F ε k ∂UniformInt.law 1) = F 0 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, DivisionRejection.kernel]

example : (∫⁻ k, (if k = 0 then 0 else ∞ : ℝ≥0∞) ∂UniformInt.law 1) = 0 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ]

example (n : ℕ) [NeZero n] : (∫⁻ _k, (∞ : ℝ≥0∞) ∂UniformInt.law n) = ∞ := by simp

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : DebiasedModulo.kernel 5 8 F ε 5 = F 0 := by
  norm_num [DebiasedModulo.kernel]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : DebiasedModulo.kernel 3 4 F ε 3 = F 0 := by
  norm_num [DebiasedModulo.kernel]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    DebiasedModulo.kernel 5 8 F ε 0 = (∫⁻ k, F k ∂UniformInt.law 5) + 2 * ε := by
  norm_num [DebiasedModulo.kernel]

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, DebiasedModulo.kernel 5 8 F ε k ∂UniformInt.law 8) =
      (3 * ((∫⁻ k, F k ∂UniformInt.law 5) + 2 * ε) +
        F 3 + F 4 + F 0 + F 1 + F 2) / 8 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, DebiasedModulo.kernel]
  simp only [ENNReal.div_eq_inv_mul]
  ring

example (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, DebiasedModulo.kernel 1 1 F ε k ∂UniformInt.law 1) = F 0 := by
  norm_num [UniformInt.lintegral_law, Finset.sum_range_succ, DebiasedModulo.kernel]

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


example (E : CoPset) (ws : List ℕ) [NeZero ws.sum]
    (F : ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂WeightedReservoirOne.law ws) ∗ I -∗
      tglWp E pl(&Occil.Weighted.weightedReservoirOne
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i) ∗ I)) :=
  frame (WeightedReservoirOne.weightedReservoirOne_distSpec E ws) F I

example (E : CoPset) (n bits : ℕ) [NeZero n] (hnw : n ≤ 2 ^ bits)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.divisionRejection #int (n : ℤ) #int (bits : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (DivisionRejection.divisionRejection_distSpec E n bits hnw) F I

example (E : CoPset) (n bits : ℕ) [NeZero n] (hnw : n ≤ 2 ^ bits)
    (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) ∗ I -∗
      tglWp E pl(&Occil.WeightedVariants.debiasedModulo #int (n : ℤ) #int (bits : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k) ∗ I)) :=
  frame (DebiasedModulo.debiasedModulo_distSpec E n bits hnw) F I

#print axioms DebiasedModulo.debiasedModulo_distSpec
#print axioms DebiasedModulo.expectation
#print axioms WordRotation.sum_cycles
#print axioms WeightedReservoirOne.weightedReservoirOne_distSpec
#print axioms WeightedReservoirOne.expectation
#print axioms WeightedReservoirOne.initial_credit
#print axioms DivisionRejection.divisionRejection_distSpec
#print axioms DivisionRejection.expectation
#print axioms WordIntervals.quotient_expectation
#print axioms WordIntervals.remainder_expectation

end

end ExpansionDiscreteAudit
