module

public import SampLib.Combinatorial.Laws.Reservoir
public import SampLib.Combinatorial.Laws.Choice
public import SampLib.Core.Laws.Permutations

@[expose] public section

/-! # Ticket credits and stream layout for Algorithm R

A uniform ticket averages the remaining scan credit. The input stream splits into the
initial reservoir prefix and the later positions that tickets may select.
-/

open scoped ENNReal

namespace SampLib.Reservoir

noncomputable section

def ticketCredit {k : ℕ} (start steps : ℕ) (s : ReservoirLaw.Slots k)
    (F : ReservoirLaw.Slots k → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ReservoirLaw.finish (start + 1) steps
    (ReservoirLaw.advance start s (Choice.position (start + 1) j)) F

theorem ticket_expectation {k : ℕ} (start steps : ℕ) (s : ReservoirLaw.Slots k)
    (F : ReservoirLaw.Slots k → ℝ≥0∞) :
    (∑ j ∈ Finset.range (start + 1), ticketCredit start steps s F j) /
      ((start + 1 : ℕ) : ℝ≥0∞) = ReservoirLaw.finish start (steps + 1) s F := by
  rw [← Fin.sum_univ_eq_sum_range (ticketCredit start steps s F) (start + 1),
    ReservoirLaw.finish_step]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [ticketCredit, Choice.position_of_lt j.val j.isLt]

theorem encoded_update {α : Type*} (decode : ℕ → α) {k : ℕ}
    (s : ReservoirLaw.Slots k) (j : Fin k) (start : ℕ) :
    (List.ofFn (decode ∘ s)).set j (decode start) =
      List.ofFn (decode ∘ Function.update s j start) := by
  rw [Function.comp_update, Permutations.ofFn_update]

theorem stream_split {α : Type*} (decode : ℕ → α) (n k : ℕ) (h : k ≤ n) :
    (List.range' 0 n).map decode =
      (List.range' 0 k).map decode ++ (List.range' k (n - k)).map decode := by
  simpa only [List.map_append, Nat.zero_add, Nat.add_sub_of_le h] using
    (congrArg (List.map decode)
      (List.range'_append_1 (s := 0) (m := k) (n := n - k))).symm

theorem stream_initial {α : Type*} (decode : ℕ → α) (k : ℕ) :
    (List.range' 0 k).map decode = List.ofFn (decode ∘ ReservoirLaw.initial k) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [ReservoirLaw.initial]

/-- The closed ordered-slot law, normalized throughout the terminating domain. -/
def law (xs : List α) (k : ℕ) (_hkn : k ≤ xs.length) :=
  ReservoirLaw.law xs.length k

instance (xs : List α) (k : ℕ) (hkn : k ≤ xs.length) :
    MeasureTheory.IsProbabilityMeasure (law xs k hkn) := by
  let : Fact (k ≤ xs.length) := ⟨hkn⟩
  change MeasureTheory.IsProbabilityMeasure (ReservoirLaw.law xs.length k)
  infer_instance

theorem zero_capacity_expectation (n : ℕ) (F : ReservoirLaw.Slots 0 → ℝ≥0∞) :
    (∫⁻ s, F s ∂ReservoirLaw.law n 0) = F (ReservoirLaw.initial 0) := by
  let : Fact (0 ≤ n) := ⟨Nat.zero_le n⟩
  have hF : F = fun _ => F (ReservoirLaw.initial 0) :=
    funext fun s => congrArg F (Subsingleton.elim s _)
  rw [hF]
  simp

end

end SampLib.Reservoir
