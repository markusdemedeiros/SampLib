module

public import SampLib.Uniform.Laws.RealCoin
public import Metrology.ProbLang.Measure
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! # Independent Bernoulli toggles of a bit list

Each input bit is toggled by its own Bernoulli draw. Independence separates the first
toggle from the remaining ones.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FlipBits

noncomputable section

/-- Toggle `x` exactly when the coin `c` is true. -/
def flip (x c : Bool) : Bool := if c then !x else x

/-- Independent Bernoulli toggles applied to the fixed input bits. -/
def law (p : unitInterval) : List Bool → Measure (List Bool)
  | [] => Measure.dirac []
  | x :: xs => ((RealCoin.law p).prod (law p xs)).map
      (fun z => flip x z.1 :: z.2)

instance (p : unitInterval) (xs : List Bool) : IsProbabilityMeasure (law p xs) := by
  induction xs with
  | nil => dsimp [law]; infer_instance
  | cons x xs IH =>
    let := IH
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Conditional credit after the first toggle. -/
def credit (p : unitInterval) (x : Bool) (xs : List Bool)
    (F : List Bool → ℝ≥0∞) (c : Bool) : ℝ≥0∞ :=
  ∫⁻ ys, F (flip x c :: ys) ∂law p xs

/-- Independence separates the first toggle from the remaining bit flips. -/
theorem expectation (p : unitInterval) (x : Bool) (xs : List Bool)
    (F : List Bool → ℝ≥0∞) :
    ∫⁻ c, credit p x xs F c ∂RealCoin.law p = ∫⁻ ys, F ys ∂law p (x :: xs) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end

end SampLib.FlipBits
