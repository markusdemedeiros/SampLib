import SampLib.Latent.Laws.DigitValue
import SampLib.Latent.LatentUniform
import SampLib.Latent.LatentViews
import SampLib.Latent.Laws.MeasuredError

/-! # A shared latent model for conditional binary digits -/

open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentDigits

noncomputable section

variable {Ω : Type} [MeasurableSpace Ω]

/-- A cached prefix must be reachable under the original joint law. -/
abbrev State (μ : Measure Ω) (digits : Ω → ℕ → Bool) :=
  {p : List Bool // μ (DigitPosterior.cylinder digits p) ≠ 0}

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (digits : Ω → ℕ → Bool)
  (hd : ∀ n, Measurable (fun x => digits x n))

/-- A new stream has not yet revealed any digits. -/
def initial : State μ digits := ⟨[], by simp⟩

/-- Observations condition the whole latent world on the cached prefix. -/
def model : LatentReal.Model Ω (State μ digits) where
  posterior p := DigitPosterior.law μ digits p.val
  probability p := DigitPosterior.probability μ digits p.val p.property
  value x := DigitPosterior.value (digits x)
  measurable_value := DigitPosterior.measurable_value hd
  refines p q := p.val <+: q.val
  refines_refl _ := List.prefix_refl _
  refines_trans := List.IsPrefix.trans
  absolutelyContinuous hpq := DigitPosterior.law_refines μ hd hpq
  error n _ := (2 ^ n : ℝ)⁻¹
  error_tendsto _ := Filter.Eventually.of_forall fun _ =>
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

theorem measurable_error : (model μ digits hd).MeasurableError :=
  fun _ => measurable_const

@[simp] theorem posterior_initial : (model μ digits hd).posterior (initial μ digits) = μ := by
  simp [model, initial]

/-- The represented law is the full pushforward of the original joint world. -/
theorem initial_law :
    (model μ digits hd).law (initial μ digits) =
      μ.map (fun x => DigitPosterior.value (digits x)) := by
  simp [LatentReal.Model.law, model, initial]

/-- Shorter rereads expose a coarser interval without forgetting the longer cache. -/
theorem interval_encloses {p q : State μ digits} {n : ℕ}
    (hread : UniformBag.readRefines p.val n q.val) :
    (model μ digits hd).Encloses q n (LatentUniform.interval q.val n) := by
  filter_upwards [DigitPosterior.ae_read_interval μ hd hread] with x hx
  refine ⟨?_, ?_⟩
  · simpa [LatentReal.RationalInterval.Contains, LatentReal.RationalInterval.lowerReal,
      LatentReal.RationalInterval.upperReal, LatentUniform.interval, model] using hx
  · change ((UniformBag.rank (q.val.take n) + 1 : ℤ) : ℝ) / (2 ^ n : ℤ) -
      (UniformBag.rank (q.val.take n) : ℝ) / (2 ^ n : ℤ) ≤ (2 ^ n : ℝ)⁻¹
    push_cast
    rw [add_div, add_sub_cancel_left, one_div]

end

end SampLib.LatentDigits
