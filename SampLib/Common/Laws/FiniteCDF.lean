import SampLib.General.InverseQuantile
import SampLib.Uniform.RationalCoin

/-! # Quantiles of integer CDFs on finite intervals -/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.FiniteCDF

noncomputable section

/-- An integer CDF with a positive common mass denominator. -/
structure Model where
  lower : ℤ
  upper : ℤ
  nonempty : lower ≤ upper
  scale : ℕ
  positive : 0 < scale
  cdf : ℤ → ℤ
  monotone : MonotoneOn cdf (Icc lower upper)
  bounded : ∀ x ∈ Icc lower upper, 0 ≤ cdf x ∧ cdf x ≤ scale
  upper_mass : cdf upper = scale

/-- Grid points whose CDF has reached the given interior rank. -/
def candidates (D : Model) (i : Fin D.scale) : Finset ℤ :=
  (Finset.Icc D.lower D.upper).filter (fun x => (i.val : ℤ) + 1 ≤ D.cdf x)

private theorem candidates_nonempty (D : Model) (i : Fin D.scale) :
    (candidates D i).Nonempty := by
  refine ⟨D.upper, ?_⟩
  simp only [candidates, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨D.nonempty, le_rfl⟩, by rw [D.upper_mass]; have := i.isLt; omega⟩

/-- The first grid point at which the cumulative mass reaches this rank. -/
def quantile (D : Model) (i : Fin D.scale) : ℤ :=
  (candidates D i).min' (candidates_nonempty D i)

/-- Quantiles lie in the grid and reach their requested cumulative mass. -/
theorem quantile_mem (D : Model) (i : Fin D.scale) :
    quantile D i ∈ Icc D.lower D.upper ∧ (i.val : ℤ) + 1 ≤ D.cdf (quantile D i) := by
  have h := Finset.min'_mem (candidates D i) (candidates_nonempty D i)
  simpa only [quantile, candidates, Finset.mem_filter, Finset.mem_Icc, Set.mem_Icc] using h

/-- Monotonicity identifies quantile comparisons with cumulative-mass comparisons. -/
theorem quantile_le_iff (D : Model) (i : Fin D.scale) (x : ℤ)
    (hx : x ∈ Icc D.lower D.upper) :
    quantile D i ≤ x ↔ (i.val : ℤ) + 1 ≤ D.cdf x := by
  constructor
  · intro h
    exact (quantile_mem D i).2.trans (D.monotone (quantile_mem D i).1 hx h)
  · intro h
    apply Finset.min'_le
    simp only [candidates, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨hx, h⟩

/-- A uniform interior rank is totalized outside its finite support. -/
def position (D : Model) (k : ℕ) : Fin D.scale :=
  letI : NeZero D.scale := ⟨D.positive.ne'⟩
  Choice.position D.scale k

theorem position_of_lt (D : Model) (k : ℕ) (hk : k < D.scale) :
    position D k = ⟨k, hk⟩ := by
  let : NeZero D.scale := ⟨D.positive.ne'⟩
  exact Choice.position_of_lt k hk

/-- The finite inverse-CDF law is the quantile pushforward of uniform ranks. -/
def law (D : Model) : Measure ℤ :=
  letI : NeZero D.scale := ⟨D.positive.ne'⟩
  InverseQuantile.law D.scale (quantile D)

instance (D : Model) : IsProbabilityMeasure (law D) := by
  let : NeZero D.scale := ⟨D.positive.ne'⟩
  dsimp [law]
  infer_instance

/-- Quantile evaluation preserves the uniform-rank expectation. -/
theorem expectation (D : Model) (F : ℤ → ℝ≥0∞) :
    (∑ k ∈ Finset.range D.scale, F (quantile D (position D k))) / D.scale =
      ∫⁻ x, F x ∂law D := by
  let : NeZero D.scale := ⟨D.positive.ne'⟩
  exact InverseQuantile.expectation D.scale (quantile D) F (measurable_of_countable _)

/-- The quantile law has the supplied CDF, including any mass at the lower endpoint. -/
theorem cdf (D : Model) (x : ℤ) (hx : x ∈ Icc D.lower D.upper) :
    law D (Iic x) = ENNReal.ofReal ((D.cdf x : ℝ) / (D.scale : ℝ)) := by
  rw [← lintegral_indicator_one measurableSet_Iic]
  simp only [Set.indicator_apply, Set.mem_Iic, Pi.one_apply]
  rw [← expectation D]
  have hsum : (∑ k ∈ Finset.range D.scale,
      (if quantile D (position D k) ≤ x then 1 else 0 : ℝ≥0∞)) =
      ∑ k ∈ Finset.range D.scale,
        RationalCoin.rankCredit (D.cdf x) (fun b => if b then 1 else 0) k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [position_of_lt D k (Finset.mem_range.mp hk)]
    have hrank : (k : ℤ) + 1 ≤ D.cdf x ↔ (k : ℤ) < D.cdf x := by omega
    simp only [quantile_le_iff D _ x hx, hrank, RationalCoin.rankCredit,
      ite_true, Bool.false_eq_true, ite_false]
  rw [hsum]
  have h := RationalCoin.expectation (D.cdf x) (D.scale : ℤ)
    (D.bounded x hx).1 (by exact_mod_cast D.positive) (D.bounded x hx).2
    (fun b => if b then (1 : ℝ≥0∞) else 0)
  simpa [RealCoin.credit, RealCoin.pmf, RationalCoin.bias] using h

/-- Integer bisection strictly reduces either remaining interval. -/
theorem midpoint_bounds (lower upper : ℤ) (h : lower < upper) :
    lower ≤ lower + (upper - lower) / 2 ∧ lower + (upper - lower) / 2 < upper := by omega

/-- A bisection bracket contains the same fixed quantile throughout the search. -/
structure Bracket (D : Model) (i : Fin D.scale) where
  lower : ℤ
  upper : ℤ
  lower_bound : D.lower ≤ lower
  upper_bound : upper ≤ D.upper
  contains : lower ≤ quantile D i ∧ quantile D i ≤ upper

namespace Bracket

variable {D : Model} {i : Fin D.scale}

def width (w : Bracket D i) : ℕ := (w.upper - w.lower).toNat

def midpoint (w : Bracket D i) : ℤ := w.lower + (w.upper - w.lower) / 2

theorem ordered (w : Bracket D i) : w.lower ≤ w.upper :=
  w.contains.1.trans w.contains.2

theorem strict_of_ne (w : Bracket D i) (h : w.lower ≠ w.upper) : w.lower < w.upper :=
  lt_of_le_of_ne w.ordered h

theorem done (w : Bracket D i) (h : w.lower = w.upper) : quantile D i = w.lower := by
  have := w.contains
  omega

theorem midpoint_mem (w : Bracket D i) (h : w.lower < w.upper) :
    midpoint w ∈ Icc D.lower D.upper := by
  have hm := midpoint_bounds w.lower w.upper h
  exact ⟨w.lower_bound.trans hm.1, hm.2.le.trans w.upper_bound⟩

def left (w : Bracket D i) (h : w.lower < w.upper)
    (hc : (i.val : ℤ) + 1 ≤ D.cdf (midpoint w)) : Bracket D i where
  lower := w.lower
  upper := midpoint w
  lower_bound := w.lower_bound
  upper_bound := (midpoint_mem w h).2
  contains := ⟨w.contains.1, (quantile_le_iff D i _ (midpoint_mem w h)).2 hc⟩

def right (w : Bracket D i) (h : w.lower < w.upper)
    (hc : ¬(i.val : ℤ) + 1 ≤ D.cdf (midpoint w)) : Bracket D i where
  lower := midpoint w + 1
  upper := w.upper
  lower_bound := by have := (midpoint_mem w h).1; omega
  upper_bound := w.upper_bound
  contains := by
    have hq : ¬quantile D i ≤ midpoint w := fun hq =>
      hc ((quantile_le_iff D i _ (midpoint_mem w h)).1 hq)
    exact ⟨by omega, w.contains.2⟩

theorem left_width_lt (w : Bracket D i) (h : w.lower < w.upper)
    (hc : (i.val : ℤ) + 1 ≤ D.cdf (midpoint w)) : width (left w h hc) < width w := by
  change (midpoint w - w.lower).toNat < (w.upper - w.lower).toNat
  have hm := midpoint_bounds w.lower w.upper h
  change w.lower ≤ midpoint w ∧ midpoint w < w.upper at hm
  omega

theorem right_width_lt (w : Bracket D i) (h : w.lower < w.upper)
    (hc : ¬(i.val : ℤ) + 1 ≤ D.cdf (midpoint w)) : width (right w h hc) < width w := by
  change (w.upper - (midpoint w + 1)).toNat < (w.upper - w.lower).toNat
  have hm := midpoint_bounds w.lower w.upper h
  change w.lower ≤ midpoint w ∧ midpoint w < w.upper at hm
  omega

/-- The original interval brackets every requested quantile. -/
def initial (D : Model) (i : Fin D.scale) : Bracket D i where
  lower := D.lower
  upper := D.upper
  lower_bound := le_rfl
  upper_bound := le_rfl
  contains := (quantile_mem D i).1

end Bracket

end

end SampLib.FiniteCDF
