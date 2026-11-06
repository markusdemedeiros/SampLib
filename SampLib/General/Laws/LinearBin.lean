import SampLib.Common.Laws.AcceptedProposal
import SampLib.Core.Laws.IntegerIntervals
import SampLib.General.Support.IntegerThreshold

/-! # A linearly interpolated density on one half-open integer bin -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LinearBin

noncomputable section

/-- Twice the exact sum of interpolated grid heights, with the right endpoint excluded. -/
structure Model where
  left : ℤ
  width : ℕ
  positive_width : 0 < width
  ha : ℕ
  hb : ℕ
  positive_mass : 0 < (width + 1) * ha + (width - 1) * hb

instance (D : Model) : NeZero D.width := ⟨D.positive_width.ne'⟩

def envelope (D : Model) : ℕ := max D.ha D.hb

/-- Interpolation numerator; division by the common width cancels on normalization. -/
def height (D : Model) (k : ℕ) : ℕ := D.ha * (D.width - k) + D.hb * k

theorem envelope_pos (D : Model) : 0 < envelope D := by
  by_contra h
  have hzero : max D.ha D.hb = 0 := by simpa [envelope] using Nat.eq_zero_of_not_pos h
  have ha : D.ha = 0 := Nat.eq_zero_of_le_zero ((le_max_left _ _).trans_eq hzero)
  have hb : D.hb = 0 := Nat.eq_zero_of_le_zero ((le_max_right _ _).trans_eq hzero)
  have := D.positive_mass
  simp [ha, hb] at this

theorem denominator_pos (D : Model) : 0 < D.width * envelope D :=
  Nat.mul_pos D.positive_width (envelope_pos D)

theorem height_le (D : Model) (k : ℕ) (hk : k < D.width) :
    height D k ≤ D.width * envelope D := by
  calc
    _ ≤ envelope D * (D.width - k) + envelope D * k :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _))
        (Nat.mul_le_mul_right _ (le_max_right _ _))
    _ = D.width * envelope D := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hk.le, Nat.mul_comm]

/-- A bounded acceptance probability, totalized by zero off the uniform support. -/
def acceptance (D : Model) (k : ℕ) : unitInterval :=
  if hk : k < D.width then
    IntegerThreshold.bias (height D k) (D.width * envelope D) (denominator_pos D)
      (height_le D k hk)
  else 0

private theorem positive_height (D : Model) : ∃ k < D.width, 0 < height D k := by
  by_cases ha : 0 < D.ha
  · exact ⟨0, D.positive_width, by simpa [height] using Nat.mul_pos ha D.positive_width⟩
  · have ha0 : D.ha = 0 := Nat.eq_zero_of_not_pos ha
    have hb : 0 < D.hb := by
      by_contra h
      have hb0 := Nat.eq_zero_of_not_pos h
      have := D.positive_mass
      simp [ha0, hb0] at this
    have hw : 1 < D.width := by
      by_contra h
      have hw : D.width = 1 := by have := D.positive_width; omega
      have := D.positive_mass
      simp [hw, ha0] at this
    exact ⟨1, hw, by simpa [height, ha0] using hb⟩

/-- A positive exact grid profile gives positive acceptance mass, even when an endpoint is zero. -/
theorem mass_ne_zero (D : Model) :
    AcceptedProposal.mass (UniformInt.law D.width) (acceptance D) ≠ 0 := by
  obtain ⟨k, hk, hh⟩ := positive_height D
  intro hzero
  have hae := (lintegral_eq_zero_iff (measurable_of_countable
    (AcceptedProposal.weight (acceptance D)))).mp hzero
  have hatom : UniformInt.law D.width {k} ≠ 0 := by
    simp [UniformInt.law, Measure.uniformOfFinset_apply_singleton, Finset.mem_range, hk]
  have hz := ae_iff_of_countable.mp hae k hatom
  have hp : 0 < AcceptedProposal.weight (acceptance D) k := by
    simp only [AcceptedProposal.weight, acceptance, dite_eq_left hk,
      IntegerThreshold.bias, RationalCoin.bias]
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (by exact_mod_cast hh) (by exact_mod_cast denominator_pos D)
  exact hp.ne' hz

/-- Accepted offsets have mass proportional to their interpolated grid density. -/
abbrev offsetLaw (D : Model) :=
  AcceptedProposal.law (UniformInt.law D.width) (acceptance D) (mass_ne_zero D)

/-- Shift the accepted offset into its signed application interval. -/
def law (D : Model) : Measure ℤ := (offsetLaw D).map (fun k : ℕ => D.left + (k : ℤ))

instance (D : Model) : IsProbabilityMeasure (law D) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

end

end SampLib.LinearBin
