module

public import SampLib.Latent.Laws.Interval
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-! # Mathematical model of a progressively observed latent real

A model assigns each oracle state a posterior on a joint latent space. Refinement keeps
every earlier almost-everywhere enclosure of the latent value.
-/

open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

/-- Mathematical state of a progressively observed joint latent draw. -/
structure Model (Ω S : Type) [MeasurableSpace Ω] where
  posterior : S → Measure Ω
  probability : ∀ s, IsProbabilityMeasure (posterior s)
  value : Ω → ℝ
  measurable_value : Measurable value
  refines : S → S → Prop
  refines_refl : ∀ s, refines s s
  refines_trans : ∀ {s t u}, refines s t → refines t u → refines s u
  absolutelyContinuous : ∀ {s t}, refines s t →
    Measure.AbsolutelyContinuous (posterior t) (posterior s)
  error : ℕ → Ω → ℝ
  error_tendsto : ∀ s, ∀ᵐ x ∂posterior s,
    Filter.Tendsto (fun n => error n x) Filter.atTop (nhds 0)

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

instance (D : Model Ω S) (s : S) : IsProbabilityMeasure (D.posterior s) := D.probability s

/-- The real-valued output law represented by a latent state. -/
def law (D : Model Ω S) (s : S) : Measure ℝ := (D.posterior s).map D.value

instance (D : Model Ω S) (s : S) : IsProbabilityMeasure (D.law s) :=
  inferInstanceAs (IsProbabilityMeasure ((D.posterior s).map D.value))

/-- The returned interval encloses the same latent value with vanishing error. -/
def Encloses (D : Model Ω S) (s : S) (n : ℕ) (I : RationalInterval) : Prop :=
  ∀ᵐ x ∂D.posterior s,
    I.Contains (D.value x) ∧ I.upperReal - I.lowerReal ≤ D.error n x

/-- Later reads preserve every earlier almost-everywhere enclosure. -/
theorem encloses_refines (D : Model Ω S) {s t : S} (h : D.refines s t)
    {n : ℕ} {I : RationalInterval} (hI : D.Encloses s n I) : D.Encloses t n I :=
  (D.absolutelyContinuous h).ae_le hI

end Model

end

end SampLib.LatentReal
