import SampLib.LatentProductModel
import SampLib.LatentAddition
import SampLib.LatentMeasuredError
import SampLib.Distributions.GammaSuccessor

/-! # Independent latent worlds for positive integer gamma shapes

Depth zero is one exponential; each successor prepends another independent
exponential world. The sum projection retains every component's cached state.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentGammaInteger

noncomputable section

open LatentReal

abbrev World (Ω : Type) : ℕ → Type
  | 0 => Ω
  | n + 1 => Ω × World Ω n

instance worldMeasurableSpace (Ω : Type) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (World Ω n)
  | 0 => inferInstanceAs (MeasurableSpace Ω)
  | n + 1 => (inferInstance : MeasurableSpace Ω).prod (worldMeasurableSpace Ω n)

abbrev State (S : Type) : ℕ → Type
  | 0 => S
  | n + 1 => S × State S n

variable {Ω S : Type} [MeasurableSpace Ω]

def model (D : Model Ω S) : (n : ℕ) → Model (World Ω n) (State S n)
  | 0 => D
  | n + 1 =>
    (ProductModel.left D (model D n)).add (ProductModel.right D (model D n))
      (ProductModel.sameWorld D (model D n))

def initial (i : S) : (n : ℕ) → State S n
  | 0 => i
  | n + 1 => (i, initial i n)

private theorem sum_law {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂) :
    ((ProductModel.left L R).add (ProductModel.right L R) (ProductModel.sameWorld L R)).law s =
      ((L.law s.1).prod (R.law s.2)).map (fun z : ℝ × ℝ => z.1 + z.2) := by
  have hsum : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
  rw [← ProductModel.law_eq_product L R s,
    Measure.map_map hsum (L.measurable_value.prodMap R.measurable_value)]
  rfl

/-- The depth-`n` sum has gamma shape `n+1` at the component exponential's rate. -/
theorem model_law (D : Model Ω S) (i : S) (rate : ℝ) (hrate : 0 < rate)
    (hD : D.law i = ProbabilityTheory.expMeasure rate) (n : ℕ) :
    (model D n).law (initial i n) = ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate := by
  induction n with
  | zero => simpa only [model, initial, Nat.zero_add, Nat.cast_one, ProbabilityTheory.expMeasure]
      using hD
  | succ n IH =>
    rw [model, initial, sum_law, hD, IH]
    change Measure.conv (ProbabilityTheory.expMeasure rate)
      (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate) = _
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      GammaSuccessor.exponential_conv_gamma ((n + 1 : ℕ) : ℝ) rate (by positivity) hrate

/-- Finite sums preserve measurable observation errors componentwise. -/
theorem measurable_error (D : Model Ω S) (hD : D.MeasurableError) (n : ℕ) :
    (model D n).MeasurableError := by
  induction n with
  | zero => exact hD
  | succ n IH =>
    intro k
    change Measurable (fun z : Ω × World Ω n => D.error k z.1 + (model D n).error k z.2)
    exact ((hD k).comp measurable_fst).add ((IH k).comp measurable_snd)

end

end SampLib.LatentGammaInteger
