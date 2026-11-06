module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! # Independent product of repeated draws

`law μ n` draws `n` independent samples from `μ` in the order the algorithm returns them.
Fubini splits each draw into the head sample and the tail expectation.
-/

open scoped ENNReal

namespace SampLib.SampleWithReplacement

noncomputable section

open MeasureTheory Measure

variable {α : Type _} [MeasurableSpace α]

theorem measurable_cons (n : ℕ) :
    Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n + 1) → α)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
      (measurable_snd : Measurable (Prod.snd : α × (Fin n → α) → (Fin n → α)))

/-- Independent draws from `μ`, in the order returned by the algorithm. -/
def law (μ : Measure α) : (n : ℕ) → Measure (Fin n → α)
  | 0 => dirac (Fin.elim0)
  | n + 1 => (μ.prod (law μ n)).map (fun z => Fin.cons z.1 z.2)

instance law_zero_prob (μ : Measure α) : IsProbabilityMeasure (law μ 0) := by
  dsimp [law]
  infer_instance

instance (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (law μ n) := by
  induction n with
  | zero => infer_instance
  | succ n IH =>
    let _ := IH
    constructor
    rw [law, Measure.map_apply (measurable_cons n) MeasurableSet.univ]
    simp

/-- Fubini expresses the independent draw as its two continuation expectations. -/
theorem lintegral_law_succ (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin (n + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ys, F ys ∂law μ (n + 1) =
      ∫⁻ x, ∫⁻ ys, F (Fin.cons x ys) ∂law μ n ∂μ := by
  rw [law, lintegral_map hF (measurable_cons n)]
  exact lintegral_prod _ (hF.comp (measurable_cons n)).aemeasurable

theorem measurable_tail (n : ℕ) (x : α)
    (F : (Fin (n + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun ys => F (Fin.cons x ys)) := by
  simpa only [Function.comp_def] using
    (hF.comp (measurable_cons n)).comp measurable_prodMk_left

theorem measurable_cont (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin (n + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun x => ∫⁻ ys, F (Fin.cons x ys) ∂law μ n) := by
  apply Measurable.lintegral_prod_right
  simpa only [Function.comp_def, Function.uncurry_def] using hF.comp (measurable_cons n)

end

end SampLib.SampleWithReplacement
