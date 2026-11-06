import SampLib.General.MarkovChain
import SampLib.General.RandomMap
import SampLib.General.RandomWalkPath
import SampLib.Combinatorial.Sattolo
import SampLib.General.PermutationSamples

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

section integer_draws
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (rows : List MarkovChain.Row)
    (hsq : ∀ r ∈ rows, r.val.length = rows.length) (n i : ℕ) (hi : i < rows.length)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂MarkovChain.law rows n i) ∗ R -∗
      tglWp E pl(&Occil.General.markovChain &(listVal MarkovChain.encodeRow rows).fst
        #int (i : ℤ) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ x : ℕ, ⌜v = Val.int x⌝ ∗ ↯ (F x) ∗ R)) :=
  frame (MarkovChain.markovChain_distSpec E rows hsq n i hi)
    F (measurable_of_countable _) R

example (E : CoPset) (rows : List MarkovChain.Row)
    (F : List ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂RandomMap.law rows) ∗ R -∗
      tglWp E pl(&Occil.General.randomMap &(listVal RandomMap.encodeRow rows).fst #())
        (fun v : Val rT => iprop(∃ xs : List ℕ,
          ⌜v = listVal (fun k : ℕ => Val.int k) xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (RandomMap.randomMap_distSpec E rows) F (measurable_of_countable _) R

example {α : Type*} (E : CoPset) (encode : α → Val rT) (xs : List α)
    (F : SattoloLaw.Cycle xs.length → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ σ, F σ ∂Sattolo.law xs) ∗ R -∗
      tglWp E pl(&Occil.sattolo &(listVal encode xs).fst)
        (fun v : Val rT => iprop(∃ σ : SattoloLaw.Cycle xs.length,
          ⌜v = listVal encode (Sattolo.output xs σ)⌝ ∗ ↯ (F σ) ∗ R)) :=
  frame (Sattolo.sattolo_distSpec E encode xs) F (measurable_of_countable _) R

example {α : Type*} (E : CoPset) (encode : α → Val rT) (xs : List α) (n : ℕ)
    (F : (Fin n → Equiv.Perm (Fin xs.length)) → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ ys, F ys ∂PermutationSamples.law xs n) ∗ R -∗
      tglWp E pl(&Occil.General.permutationSamples &(listVal encode xs).fst #int (n : ℤ) #())
        (fun v : Val rT => iprop(∃ ys : Fin n → Equiv.Perm (Fin xs.length),
          ⌜v = listVal (fun σ => listVal encode (Shuffle.output xs σ)) (List.ofFn ys)⌝ ∗
            ↯ (F ys) ∗ R)) :=
  frame (PermutationSamples.permutationSamples_distSpec E encode xs n)
    F (measurable_of_countable _) R

end integer_draws

example (E : CoPset) (matrix initial : Val rT) (F : Unit → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (F ()) ∗ R -∗ tglWp E pl(&Occil.General.markovChain &matrix.fst &initial.fst #0)
      (fun v : Val rT => iprop(∃ u : Unit, ⌜v = initial⌝ ∗ ↯ (F u) ∗ R)) := by
  simpa using frame (MarkovChain.markovChain_zero_distSpec E matrix initial)
    F (measurable_of_countable _) R

example (E : CoPset) (μ : MeasureTheory.Measure ℤ) [MeasureTheory.IsProbabilityMeasure μ]
    (increment : Val rT) (h : IsDistSpec (GF := GF) E pl(&increment.fst #()) μ Val.int)
    (initial : ℤ) (n : ℕ) (F : List ℤ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ xs, F xs ∂RandomWalkPath.law μ initial n) ∗ R -∗
      tglWp E pl(&Occil.General.randomWalkPath &increment.fst #int initial #int (n : ℤ))
        (fun v : Val rT => iprop(∃ xs : List ℤ,
          ⌜v = listVal (fun k : ℤ => Val.int k) xs⌝ ∗ ↯ (F xs) ∗ R)) :=
  frame (RandomWalkPath.randomWalkPath_distSpec E μ increment h initial n)
    F (measurable_of_countable _) R

open MeasureTheory

example (μ : Measure ℤ) (i : ℤ) : RandomWalkPath.law μ i 0 = Measure.dirac [i] := by
  simp [RandomWalkPath.law, SampleWithReplacement.law,
    Measure.map_dirac' (measurable_of_countable _)]

example : RandomWalkPath.law (Measure.dirac (-2)) 3 3 = Measure.dirac [3, 1, -1, -3] := by
  simp [RandomWalkPath.law, SampleWithReplacement.law, Measure.dirac_prod_dirac,
    Measure.map_dirac, List.ofFn_succ, Fin.cons]
  rfl

example (μ : Measure ℤ) [IsProbabilityMeasure μ] (i : ℤ) (n : ℕ) :
    (∫⁻ _ : List ℤ, (∞ : ℝ≥0∞) ∂RandomWalkPath.law μ i n) = ∞ := by simp

example (rows : List MarkovChain.Row) (n i : ℕ) :
    (∫⁻ _ : ℕ, (∞ : ℝ≥0∞) ∂MarkovChain.law rows n i) = ∞ := by simp

example (rows : List MarkovChain.Row) :
    (∫⁻ _ : List ℕ, (∞ : ℝ≥0∞) ∂RandomMap.law rows) = ∞ := by simp

example : RandomMap.law [] = Measure.dirac [] := rfl

example (n : ℕ) : (∫⁻ _ : SattoloLaw.Cycle n, (∞ : ℝ≥0∞) ∂SattoloLaw.law n) = ∞ := by
  simp

example : Fintype.card (SattoloLaw.Cycle 5) = 24 := by rw [SattoloLaw.card_cycle]; decide

example (σ : SattoloLaw.Cycle 4) : SattoloLaw.law 4 {σ} = 1 / 6 := by
  norm_num [SattoloLaw.law_singleton]

example : ¬SattoloLaw.FullCycle (1 : Equiv.Perm (Fin 3)) := by
  intro h
  have he := (h 0 1).eq_of_left (by rfl)
  exact (by decide : (0 : Fin 3) ≠ 1) he

example (σ : SattoloLaw.Cycle 0) : Sattolo.output ([] : List ℤ) σ = [] := rfl

example (σ : SattoloLaw.Cycle 2) : Sattolo.output ([8, 8] : List ℤ) σ = [8, 8] := by
  have h (i : Fin 2) : ([8, 8] : List ℤ).get i = 8 := by fin_cases i <;> rfl
  unfold Sattolo.output
  rw [show (([8, 8] : List ℤ).get ∘ σ.val) = (fun _ => 8) from
    funext (fun i => h (σ.val i))]
  rfl

example {α : Type*} (xs : List α) :
    (∫⁻ _ : Fin 0 → Equiv.Perm (Fin xs.length), (7 : ℝ≥0∞)
      ∂PermutationSamples.law xs 0) = 7 := by simp

example {α : Type*} (xs : List α) (n : ℕ) :
    (∫⁻ _ : Fin n → Equiv.Perm (Fin xs.length), (∞ : ℝ≥0∞)
      ∂PermutationSamples.law xs n) = ∞ := by simp

private def alternating : List MarkovChain.Row :=
  [⟨[0, 1], by decide⟩, ⟨[1, 0], by decide⟩]

example : MarkovChain.law alternating 3 0 = Measure.dirac 1 := by
  simp [MarkovChain.law, FiniteKernels.iterate, MarkovChain.kernel, MarkovChain.row,
    alternating, WeightedChoice.law, WeightedChoice.category, UniformInt.law,
    Measure.uniformOfFinset, Measure.map_dirac,
    Measure.dirac_bind (measurable_of_countable _)]

example : RandomMap.law alternating = Measure.dirac [1, 0] := by
  simp [RandomMap.law, alternating, WeightedChoice.law, WeightedChoice.category,
    UniformInt.law, Measure.uniformOfFinset, Measure.map_dirac, Measure.dirac_prod_dirac]

example (n : ℕ) (ys : Fin n → Equiv.Perm (Fin 0)) :
    List.ofFn (fun i => Shuffle.output ([] : List ℤ) (ys i)) = List.replicate n [] := by
  simp [Shuffle.output]

end
end ReviewExpansionStructured

#print axioms SampLib.MarkovChain.markovChain_distSpec
#print axioms SampLib.MarkovChain.markovChain_zero_distSpec
#print axioms SampLib.RandomMap.randomMap_distSpec
#print axioms SampLib.RandomWalkPath.randomWalkPath_distSpec
#print axioms SampLib.Sattolo.sattolo_distSpec
#print axioms SampLib.PermutationSamples.permutationSamples_distSpec
#print axioms SampLib.FiniteKernels.invariant_of_detailed_balance
#print axioms SampLib.SattoloLaw.expectation
#print axioms SampLib.SattoloLaw.card_cycle
