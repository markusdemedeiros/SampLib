import SampLib.Samplers.Reservoir
import SampLib.Samplers.RandomGraph

open ProbLang
open scoped ENNReal

namespace ReviewExpansionStructured

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A caller retains its own resource while spending the expected sampler credit. -/
theorem frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : List RandomGraph.Edge → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂RandomGraph.law p (RandomGraph.complete n)) ∗ R -∗
      tglWp E pl(&Occil.randomGraph #int (n : ℤ) &coin.fst)
        (fun v : Val rT => iprop(∃ ys : List RandomGraph.Edge,
          ⌜v = listVal RandomGraph.edgeVal ys⌝ ∗ ↯ (F ys) ∗ R)) :=
  frame (RandomGraph.randomGraph_distSpec E p coin hc n)
    F (measurable_of_countable _) R

example {α : Type*} [ProbLangDist.IsUniformInt rT] (E : CoPset)
    (encode : α → Val rT) (xs : List α) (k : ℕ) (hk : k ≤ xs.length)
    (F : ReservoirLaw.Slots k → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ slots, F slots ∂Reservoir.law xs k hk) ∗ R -∗
      tglWp E pl(&Occil.reservoir &(listVal encode xs).fst #int (k : ℤ))
        (fun v : Val rT => iprop(∃ slots : ReservoirLaw.Slots k,
          ⌜v = Reservoir.output encode xs slots⌝ ∗ ↯ (F slots) ∗ R)) :=
  frame (Reservoir.reservoir_distSpec E encode xs k hk) F (measurable_of_countable _) R

open MeasureTheory RandomGraph

example (p : unitInterval) (F : List Edge → ℝ≥0∞) :
    (∫⁻ ys, F ys ∂law p (complete 0)) = F [] := by simp [complete, edges]

example (p : unitInterval) (F : List Edge → ℝ≥0∞) :
    (∫⁻ ys, F ys ∂law p (complete 1)) = F [] := by simp [complete, edges, columns]

example : complete 3 = [(0, 1), (0, 2), (1, 2)] := rfl

example (n a b : ℕ) : (a, b) ∈ complete n ↔ a < b ∧ b < n := by
  simp [complete]

example (n : ℕ) : (∫⁻ ys, (if ys = [] then 7 else ∞ : ℝ≥0∞)
    ∂law 0 (complete n)) = 7 := by simp

example (n : ℕ) : (∫⁻ ys, (if ys = complete n then 7 else ∞ : ℝ≥0∞)
    ∂law 1 (complete n)) = 7 := by simp

private def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

example : (∫⁻ ys, (if ys = [(0, 1), (1, 2)] then 1 else 0 : ℝ≥0∞)
    ∂law half (complete 3)) = 1 / 8 := by
  change (∫⁻ ys, (if ys = [(0, 1), (1, 2)] then 1 else 0 : ℝ≥0∞)
    ∂law half ((0, 1) :: (0, 2) :: (1, 2) :: [])) = 1 / 8
  norm_num [← expectation, credit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, half,
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← ENNReal.mul_inv (a := 2) (b := 2) (by simp) (by simp),
    ← ENNReal.mul_inv (a := 2) (b := 2 * 2) (by simp) (by simp)]
  norm_num

example (p : unitInterval) (n : ℕ) :
    (∫⁻ _ : List Edge, (∞ : ℝ≥0∞) ∂law p (complete n)) = ∞ := by simp

example : ReservoirLaw.law 5 2 {![2, 4]} = (20 : ℝ≥0∞)⁻¹ := by
  rw [ReservoirLaw.law_singleton_closed (by decide)]
  norm_num [ReservoirLaw.Admissible, Function.Injective, ReservoirLaw.lateCount,
    Fin.forall_fin_two, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton,
    Nat.choose, Nat.factorial]

example : ReservoirLaw.law 5 2 {![0, 4]} = (10 : ℝ≥0∞)⁻¹ := by
  rw [ReservoirLaw.law_singleton_closed (by decide)]
  norm_num [ReservoirLaw.Admissible, Function.Injective, ReservoirLaw.lateCount,
    Fin.forall_fin_two, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton,
    Nat.choose, Nat.factorial]

example : ReservoirLaw.law 5 2 {![4, 0]} = 0 := by
  rw [ReservoirLaw.law_singleton_closed (by decide)]
  norm_num [ReservoirLaw.Admissible, Fin.forall_fin_two]

example : ReservoirLaw.law 5 2 {![4, 4]} = 0 := by
  rw [ReservoirLaw.law_singleton_closed (by decide)]
  norm_num [ReservoirLaw.Admissible, Function.Injective, Fin.forall_fin_two]

example (k : ℕ) : ReservoirLaw.law k k = Measure.dirac (ReservoirLaw.initial k) :=
  ReservoirLaw.law_initial k

example (n : ℕ) (F : ReservoirLaw.Slots 0 → ℝ≥0∞) :
    (∫⁻ s, F s ∂ReservoirLaw.law n 0) = F (ReservoirLaw.initial 0) := by
  rw [← ReservoirLaw.finish_bridge (Nat.zero_le n)]
  have hF : F = fun _ => F (ReservoirLaw.initial 0) :=
    funext (fun s => congrArg F (Subsingleton.elim s _))
  rw [hF]
  simp

example {α : Type*} (xs : List α) (k : ℕ) (hk : k ≤ xs.length) :
    (∫⁻ _ : ReservoirLaw.Slots k, (∞ : ℝ≥0∞) ∂Reservoir.law xs k hk) = ∞ := by simp

example : Reservoir.output (rT := rT) Val.int ([2, 5, 2] : List ℤ)
    (ReservoirLaw.initial 3) = listVal Val.int [2, 5, 2] := by rfl

example (s : ReservoirLaw.Slots 0) :
    Reservoir.output (rT := rT) Val.int ([] : List ℤ) s = listVal Val.int [] := rfl

example {n k : ℕ} (hk : k ≤ n) (F : ReservoirLaw.Slots k → ℝ≥0∞) :
    ReservoirLaw.finish k (n - k) (ReservoirLaw.initial k) F =
      ∫⁻ s, F s ∂ReservoirLaw.law n k := ReservoirLaw.finish_bridge hk F

end
end ReviewExpansionStructured

#print axioms SampLib.RandomGraph.randomGraph_distSpec
#print axioms SampLib.RandomGraph.expectation
#print axioms SampLib.RandomGraph.edges_ordered
#print axioms SampLib.RandomGraph.law_zero
#print axioms SampLib.RandomGraph.law_one

#print axioms SampLib.Reservoir.reservoir_distSpec
#print axioms SampLib.ReservoirLaw.incoming_weight
#print axioms SampLib.ReservoirLaw.finish_bridge
#print axioms SampLib.ReservoirLaw.law_singleton_closed
