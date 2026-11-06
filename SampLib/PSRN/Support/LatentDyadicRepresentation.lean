import SampLib.PSRN.Support.LatentRepresentedSpec
import SampLib.PSRN.Laws.FloorUncertainty

/-! # Canonical dyadic floor-cell representations

The cell enclosing a real has denominator `2^n`, lower numerator `floor(2^n*x)`,
and adjacent upper numerator. This representation also covers negative values.
-/

open MeasureTheory Filter Topology

namespace SampLib.LatentReal

noncomputable section

/-- The closed dyadic cell selected by the real floor convention. -/
def dyadicInterval (n : ℕ) (x : ℝ) : RationalInterval :=
  let lo := ⌊x * (((2 : ℤ) ^ n : ℤ) : ℝ)⌋
  ⟨lo, lo + 1, (2 : ℤ) ^ n, by positivity, by omega⟩

theorem dyadicInterval_contains (n : ℕ) (x : ℝ) : (dyadicInterval n x).Contains x := by
  have hd : (0 : ℝ) < (((2 : ℤ) ^ n : ℤ) : ℝ) := by positivity
  constructor
  · exact (div_le_iff₀ hd).mpr (Int.floor_le _)
  · apply (le_div_iff₀ hd).mpr
    simpa only [dyadicInterval, Int.cast_add, Int.cast_one] using
      (Int.lt_floor_add_one (x * (((2 : ℤ) ^ n : ℤ) : ℝ))).le

@[simp] theorem dyadicInterval_width (n : ℕ) (x : ℝ) :
    (dyadicInterval n x).width = (1 / 2 : ℝ) ^ n := by
  calc
    _ = 1 / (((2 : ℤ) ^ n : ℤ) : ℝ) := by
      dsimp [RationalInterval.width, RationalInterval.lowerReal, RationalInterval.upperReal,
        dyadicInterval]
      push_cast
      ring
    _ = _ := by simp

theorem dyadicInterval_approximates (x : ℝ) :
    RationalInterval.Approximates (fun n => dyadicInterval n x) x := by
  refine ⟨fun n => dyadicInterval_contains n x, ?_⟩
  simp_rw [dyadicInterval_width]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Every real projection has a canonical measurable dyadic floor-cell schedule. -/
def Model.dyadicRepresentation (D : Model Ω S) : Representation D where
  interval n x := dyadicInterval n (D.value x)
  measurable_lower _n := (D.measurable_value.mul_const _).floor
  measurable_upper _n := ((D.measurable_value.mul_const _).floor).add_const 1
  measurable_denominator _ := measurable_const
  approximates _ := ae_of_all _ fun x => dyadicInterval_approximates (D.value x)

/-- Exact endpoint-format facts identify the represented interval without another program proof. -/
theorem Model.observed_dyadic_of_format (D : Model Ω S) (s : S) (n : ℕ) (I : RationalInterval)
    (hdenominator : I.denominator = (2 : ℤ) ^ n) (hgap : I.upper = I.lower + 1)
    (hfloor : ∀ᵐ x ∂D.posterior s, ⌊D.value x * (((2 : ℤ) ^ n : ℤ) : ℝ)⌋ = I.lower) :
    D.dyadicRepresentation.Observed s n I := by
  filter_upwards [hfloor] with x hx
  change I = dyadicInterval n (D.value x)
  cases I with
  | mk lo hi denominator hpos hordered =>
    dsimp only at hdenominator hgap hx
    subst hi
    subst denominator
    simp only [dyadicInterval, hx]

end

end SampLib.LatentReal
