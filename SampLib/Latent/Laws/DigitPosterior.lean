module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Conditional laws of a memoized digit stream

A prefix records information about one underlying draw. Its children partition
that information, so arbitrary joint continuation credit disintegrates over the
next digit. No independence or nonatomicity of the digits is assumed.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.DigitPosterior

noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

/-- The event that the latent stream begins with a specified finite prefix. -/
def cylinder (digits : Ω → ℕ → Bool) : List Bool → Set Ω
  | [] => univ
  | b :: p => {x | digits x 0 = b} ∩ cylinder (fun x n => digits x (n + 1)) p

omit [MeasurableSpace Ω] in
@[simp] theorem cylinder_nil (digits : Ω → ℕ → Bool) : cylinder digits [] = univ := rfl

theorem measurableSet_cylinder {digits : Ω → ℕ → Bool}
    (hd : ∀ n, Measurable (fun x => digits x n)) (p : List Bool) :
    MeasurableSet (cylinder digits p) := by
  induction p generalizing digits with
  | nil => exact MeasurableSet.univ
  | cons b p ih =>
    exact (hd 0 (.singleton b)).inter (ih (fun n => hd (n + 1)))

omit [MeasurableSpace Ω] in
theorem cylinder_append (digits : Ω → ℕ → Bool) (p q : List Bool) :
    cylinder digits (p ++ q) =
      cylinder digits p ∩ cylinder (fun x n => digits x (n + p.length)) q := by
  induction p generalizing digits with
  | nil => simp [cylinder]
  | cons b p ih =>
    simp only [List.cons_append, cylinder, ih, List.length_cons, inter_assoc]
    congr 2

omit [MeasurableSpace Ω] in
theorem cylinder_extend (digits : Ω → ℕ → Bool) (p : List Bool) (b : Bool) :
    cylinder digits (p ++ [b]) = cylinder digits p ∩ {x | digits x p.length = b} := by
  simp [cylinder_append, cylinder]

omit [MeasurableSpace Ω] in
theorem cylinder_mono {digits : Ω → ℕ → Bool} {p q : List Bool} (hp : p <+: q) :
    cylinder digits q ⊆ cylinder digits p := by
  rcases hp with ⟨r, rfl⟩
  rw [cylinder_append]
  exact inter_subset_left

/-- Zero-mass prefixes have the zero law; reachable states will exclude them. -/
def law (μ : Measure Ω) (digits : Ω → ℕ → Bool) (p : List Bool) : Measure Ω :=
  μ[|cylinder digits p]

instance (μ : Measure Ω) (digits : Ω → ℕ → Bool) (p : List Bool) :
    IsZeroOrProbabilityMeasure (law μ digits p) :=
  inferInstanceAs (IsZeroOrProbabilityMeasure μ[|cylinder digits p])

@[simp] theorem law_nil (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) : law μ digits [] = μ := by simp [law]

theorem probability (μ : Measure Ω) [IsFiniteMeasure μ] (digits : Ω → ℕ → Bool)
    (p : List Bool) (hp : μ (cylinder digits p) ≠ 0) :
    IsProbabilityMeasure (law μ digits p) := cond_isProbabilityMeasure hp

theorem ae_mem {digits : Ω → ℕ → Bool} (μ : Measure Ω)
    (hd : ∀ n, Measurable (fun x => digits x n)) (p : List Bool) :
    ∀ᵐ x ∂law μ digits p, x ∈ cylinder digits p :=
  ae_cond_mem (measurableSet_cylinder hd p)

/-- Extending a prefix preserves every fact already known about the same draw. -/
theorem law_refines (μ : Measure Ω) [IsFiniteMeasure μ]
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    {p q : List Bool} (hp : p <+: q) : law μ digits q ≪ law μ digits p := by
  have hcond : (law μ digits p)[|cylinder digits q] = law μ digits q := by
    rw [law, cond_cond_eq_cond_inter (measurableSet_cylinder hd p)
      (measurableSet_cylinder hd q), inter_eq_right.mpr (cylinder_mono hp)]
    rfl
  rw [← hcond]
  exact cond_absolutelyContinuous

/-- A fresh digit conditions the current posterior on the corresponding child. -/
theorem law_extend (μ : Measure Ω) [IsFiniteMeasure μ]
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) (b : Bool) :
    (law μ digits p)[|{x | digits x p.length = b}] = law μ digits (p ++ [b]) := by
  rw [law, cond_cond_eq_cond_inter (measurableSet_cylinder hd p)
    (s := cylinder digits p) (t := {x | digits x p.length = b})
    (hd p.length (.singleton b)), ← cylinder_extend]
  rfl

/-- The next-bit kernel reconstructs the current joint law, including zero-mass children. -/
theorem split (μ : Measure Ω) [IsFiniteMeasure μ]
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) :
    ∑ b : Bool, (law μ digits p) {x | digits x p.length = b} •
      law μ digits (p ++ [b]) = law μ digits p := by
  have h := sum_meas_smul_cond_fiber (hd p.length) (law μ digits p)
  change (∑ b : Bool, (law μ digits p) {x | digits x p.length = b} •
    (law μ digits p)[|{x | digits x p.length = b}]) = _ at h
  simpa only [law_extend μ hd] using h

/-- Expectation preservation for arbitrary, possibly infinite, continuation credit. -/
theorem expectation_preservation (μ : Measure Ω) [IsFiniteMeasure μ]
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    (p : List Bool) (F : Ω → ℝ≥0∞) :
    ∑ b : Bool, (law μ digits p) {x | digits x p.length = b} *
      ∫⁻ x, F x ∂law μ digits (p ++ [b]) = ∫⁻ x, F x ∂law μ digits p := by
  have h := congrArg (fun ν : Measure Ω => ∫⁻ x, F x ∂ν) (split μ hd p)
  simpa only [lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul] using h

end

end SampLib.DigitPosterior
