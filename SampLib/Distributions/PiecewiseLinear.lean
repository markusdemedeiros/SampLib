import SampLib.Distributions.LinearBin
import SampLib.Distributions.LinearGridMass
import SampLib.Distributions.PositiveWeights

/-! # Exact integer-grid laws for piecewise linear densities -/

open scoped BigOperators ENNReal

namespace SampLib.PiecewiseLinear

noncomputable section

/-- Twice a bin's sum of linearly interpolated heights on its half-open grid. -/
def binWeight (a b : ℤ × ℕ) : ℕ :=
  let w := (b.1 - a.1).toNat
  (w + 1) * a.2 + (w - 1) * b.2

/-- The bin coefficient is twice its exact half-open grid density mass. -/
theorem binWeight_mass (a b : ℤ × ℕ) (hab : a.1 < b.1) :
    let w := (b.1 - a.1).toNat
    2 * (Finset.sum (Finset.range w) (fun k => a.2 * (w - k) + b.2 * k)) =
      w * binWeight a b :=
  LinearGridMass.twice_sum _ _ _ (by omega)

def weights : List (ℤ × ℕ) → List ℕ
  | a :: b :: xs => binWeight a b :: weights (b :: xs)
  | _ => []

/-- Nonnegative vertex heights on a strictly increasing integer partition. -/
structure Model where
  vertices : List (ℤ × ℕ)
  increasing : ∀ i, i + 1 < vertices.length →
    (vertices[i]?.getD (0, 0)).1 < (vertices[i + 1]?.getD (0, 0)).1
  positive : (weights vertices).sum ≠ 0

theorem weights_length (xs : List (ℤ × ℕ)) : (weights xs).length = xs.length - 1 := by
  induction xs with
  | nil => simp [weights]
  | cons a xs IH =>
    cases xs with
    | nil => simp [weights]
    | cons b xs => simpa [weights] using IH

theorem weight_eq (xs : List (ℤ × ℕ)) (i : ℕ) (hi : i < (weights xs).length) :
    (weights xs)[i]?.getD 0 = binWeight (xs[i]?.getD (0, 0)) (xs[i + 1]?.getD (0, 0)) := by
  induction xs generalizing i with
  | nil => simp [weights] at hi
  | cons a xs IH =>
    cases xs with
    | nil => simp [weights] at hi
    | cons b xs =>
      cases i with
      | zero => simp [weights]
      | succ i =>
        simpa only [weights, List.getElem?_cons_succ, Nat.succ_eq_add_one] using
          IH i (by simpa [weights] using hi)

instance (D : Model) : NeZero (weights D.vertices).sum := ⟨D.positive⟩

theorem bin_bounds (D : Model) (i : ℕ) (hi : i < (weights D.vertices).length) :
    i < D.vertices.length ∧ i + 1 < D.vertices.length := by
  rw [weights_length] at hi
  omega

/-- A selected positive-weight bin has a positive exact grid profile. -/
def bin (D : Model) (i : ℕ) (hi : i < (weights D.vertices).length)
    (hp : 0 < (weights D.vertices)[i]?.getD 0) : LinearBin.Model where
  left := (D.vertices[i]?.getD (0, 0)).1
  width := ((D.vertices[i + 1]?.getD (0, 0)).1 -
    (D.vertices[i]?.getD (0, 0)).1).toNat
  positive_width := by have := D.increasing i (bin_bounds D i hi).2; omega
  ha := (D.vertices[i]?.getD (0, 0)).2
  hb := (D.vertices[i + 1]?.getD (0, 0)).2
  positive_mass := by simpa only [weight_eq D.vertices i hi, binWeight] using hp

section mathematics

open MeasureTheory Measure

def binLaw (D : Model) (i : ℕ) : Measure ℤ :=
  if h : i < (weights D.vertices).length ∧ 0 < (weights D.vertices)[i]?.getD 0 then
    LinearBin.law (bin D i h.1 h.2)
  else dirac 0

instance (D : Model) (i : ℕ) : IsProbabilityMeasure (binLaw D i) := by
  unfold binLaw
  split <;> infer_instance

/-- Choose a bin by its exact grid mass, then normalize its interpolated heights. -/
def law (D : Model) : Measure ℤ :=
  (WeightedChoice.law (weights D.vertices)).bind (binLaw D)

instance (D : Model) : IsProbabilityMeasure (law D) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Conditioning on the selected bin preserves the piecewise linear expectation. -/
theorem expectation (D : Model) (F : ℤ → ℝ≥0∞) :
    ∫⁻ i, ∫⁻ x, F x ∂binLaw D i ∂WeightedChoice.law (weights D.vertices) =
      ∫⁻ x, F x ∂law D := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

end mathematics

end

end SampLib.PiecewiseLinear
