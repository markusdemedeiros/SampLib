import SampLib.LatentMeasuredError
import SampLib.Distributions.LatentReal.IntervalRoots

/-! # The shared latent world of a nonnegative deferred root

The returned bisection interval has dyadic width, independent of the source's
observation schedule. Source comparisons require a separate explicit domain.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- A root retains the source posterior, cache refinements, and joint latent world. -/
def Model.nthRoot (D : Model Ω S) (degree : ℕ) : Model Ω S :=
  { D with
    value := fun x => root degree (D.value x)
    measurable_value := by unfold root; exact D.measurable_value.pow_const _
    error := fun n _ => (1 / 2 : ℝ) ^ n
    error_tendsto := fun _ => Filter.Eventually.of_forall fun _ =>
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num) }

theorem Model.MeasurableError.nthRoot (D : Model Ω S) (degree : ℕ) :
    (D.nthRoot degree).MeasurableError := fun _ => measurable_const

namespace Root

/-- A sufficient domain makes every rational-power comparison terminate almost surely. -/
def Admissible (D : Model Ω S) (degree : ℕ) (s : S) : Prop :=
  (∀ᵐ x ∂D.posterior s, 0 ≤ D.value x) ∧
    ∀ (a b : ℤ), 0 ≤ a → 0 < b →
      ∀ᵐ x ∂D.posterior s, D.value x ≠ ((a : ℝ) / b) ^ degree

/-- Refining an already admissible cache preserves the source comparison domain. -/
theorem Admissible.refines {D : Model Ω S} {degree : ℕ} {s t : S}
    (h : Admissible D degree s) (hst : D.refines s t) : Admissible D degree t :=
  ⟨(D.absolutelyContinuous hst).ae_le h.1,
    fun a b ha hb => (D.absolutelyContinuous hst).ae_le (h.2 a b ha hb)⟩

/-- Atomlessness discharges all power-threshold exclusions without independence assumptions. -/
theorem Admissible.of_atomless (D : Model Ω S) (degree : ℕ) (s : S)
    [NullSingletonClass (D.law s)] (hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x) :
    Admissible D degree s :=
  ⟨hnonneg, fun a b _ _ => ae_of_ae_map D.measurable_value.aemeasurable
    ((D.law s).ae_ne (((a : ℝ) / b) ^ degree))⟩

end Root

end

end SampLib.LatentReal
