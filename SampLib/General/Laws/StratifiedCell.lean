import SampLib.General.Laws.Stratified1D

/-! # Stratified grid cell law

Successive base-`bins` digits of the cell label select the coordinate strata.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.StratifiedCell

noncomputable section

/-- Uniform coordinates in the strata selected by the cell's base digits. -/
def law (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) :
    ℕ → ℕ → Measure (List ℤ)
  | 0, _ => Measure.dirac []
  | n + 1, cell => ((law scale bins hb h n (cell / bins)).prod
      (Stratified1D.coordinate scale bins hb h (cell % bins))).map (fun z => z.2 :: z.1)

instance (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (n cell : ℕ) :
    IsProbabilityMeasure (law scale bins hb h n cell) := by
  induction n generalizing cell with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH (cell / bins)
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Independence separates a coordinate's stratum from the remaining digits. -/
theorem expectation (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (n cell : ℕ) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ x, F (x :: ys) ∂Stratified1D.coordinate scale bins hb h (cell % bins)
        ∂law scale bins hb h n (cell / bins) =
      ∫⁻ ys, F ys ∂law scale bins hb h (n + 1) cell := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end

end SampLib.StratifiedCell
