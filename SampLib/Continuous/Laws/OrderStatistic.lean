module

public import SampLib.Common.Laws.Sorting
public import Metrology.ProbLang.Reals
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! # Independent unit-uniform samples and their order statistics

The sample is a nested product of unit uniforms. Sorting is canonical, so equal values
retain their multiplicities.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.OrderStatistic

noncomputable section

/-- A fixed number of real samples, with the usual finite product sigma-algebra. -/
abbrev Sample : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × Sample n

instance sampleMeasurableSpace : (n : ℕ) → MeasurableSpace (Sample n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => by
      letI := sampleMeasurableSpace n
      exact inferInstanceAs (MeasurableSpace (ℝ × Sample n))

instance sampleMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Sample n) := by
  induction n with
  | zero => dsimp [Sample, sampleMeasurableSpace]; infer_instance
  | succ n IH =>
    let := IH
    change MeasurableSingletonClass (ℝ × Sample n)
    infer_instance

def samples : (n : ℕ) → Sample n → List ℝ
  | 0, _ => []
  | n + 1, s => s.1 :: samples n s.2

def sorted (n : ℕ) (s : Sample n) : List ℝ :=
  (samples n s).insertionSort (· ≤ ·)

@[simp] theorem samples_length (n : ℕ) (s : Sample n) : (samples n s).length = n := by
  induction n with
  | zero => rfl
  | succ n IH => simp [samples, IH]

@[simp] theorem sorted_length (n : ℕ) (s : Sample n) : (sorted n s).length = n := by
  simp [sorted, List.length_insertionSort]

theorem sorted_perm (n : ℕ) (s : Sample n) : (sorted n s).Perm (samples n s) :=
  List.perm_insertionSort _ _

theorem sorted_ordered (n : ℕ) (s : Sample n) : (sorted n s).Pairwise (· ≤ ·) :=
  List.pairwise_insertionSort _ _

theorem sorted_unique (n : ℕ) (s : Sample n) (xs : List ℝ)
    (hp : xs.Perm (samples n s)) (hs : xs.Pairwise (· ≤ ·)) : xs = sorted n s :=
  (hp.trans (sorted_perm n s).symm).eq_of_pairwise' hs (sorted_ordered n s)

abbrev rankIndex (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (s : Sample n) :
    Fin (sorted n s).length := ⟨k - 1, by rw [sorted_length]; omega⟩

def selected (n k : ℕ) (hk : 0 < k ∧ k ≤ n) (s : Sample n) : ℝ :=
  (sorted n s).get (rankIndex n k hk s)

section mathematics

open MeasureTheory

/-- Independent unit-uniform draws, before sorting or selecting a rank. -/
def law : (n : ℕ) → Measure (Sample n)
  | 0 => Measure.dirac ()
  | n + 1 => LawfulProbLangℝ.unifUnit.prod (law n)

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  induction n with
  | zero => dsimp [law, sampleMeasurableSpace]; infer_instance
  | succ n IH =>
    let := IH
    dsimp only [law]
    change IsProbabilityMeasure (LawfulProbLangℝ.unifUnit.prod (law n))
    infer_instance

def credit (n : ℕ) (F : Sample (n + 1) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ s, F (x, s) ∂law n

theorem measurable_credit (n : ℕ) (F : Sample (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (credit n F) := hF.lintegral_prod_right'

/-- Tonelli conditions the iid vector on its first coordinate. -/
theorem expectation (n : ℕ) (F : Sample (n + 1) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, credit n F x ∂LawfulProbLangℝ.unifUnit = ∫⁻ s, F s ∂law (n + 1) := by
  exact (lintegral_prod _ hF.aemeasurable).symm

end mathematics

end

end SampLib.OrderStatistic
