import SampLib.LatentRootModel

/-! # Finite tail credit for the root oracle's expanding upper bracket

One positive function of the finite source value controls all doubling tails.
Its shrinking uncertainty bands fund a single global proof horizon.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def tailDistance (D : Model Ω S) (x : Ω) : ℝ := 1 / (1 + |D.value x|)

private theorem measurable_tailDistance (D : Model Ω S) : Measurable (tailDistance D) :=
  measurable_const.div (measurable_const.add D.measurable_value.abs)

private theorem tailDistance_pos (D : Model Ω S) (x : Ω) : 0 < tailDistance D x := by
  unfold tailDistance
  positivity

/-- A measured envelope containing every unresolved upper-bracket tail. -/
def tailBand (D : Model Ω S) (n : ℕ) : Set Ω :=
  LatentComparisonUncertainty.band (tailDistance D) (fun _ => 0)
    (fun n _ => (1 / 2 : ℝ) ^ n) n

theorem measurableSet_tailBand (D : Model Ω S) (n : ℕ) : MeasurableSet (tailBand D n) :=
  LatentComparisonUncertainty.measurableSet_band (measurable_tailDistance D)
    measurable_const (fun _ => measurable_const) n

def horizonCredit (D : Model Ω S) (N : ℕ) (F : Ω → ℝ≥0∞) (x : Ω) : ℝ≥0∞ :=
  F x + (tailBand D N).indicator (fun _ => 1) x

theorem measurable_horizonCredit (D : Model Ω S) (N : ℕ) (F : Ω → ℝ≥0∞)
    (hF : Measurable F) : Measurable (horizonCredit D N F) :=
  hF.add (measurable_const.indicator (measurableSet_tailBand D N))

/-- Auxiliary bracket credit costs only the source's diminishing tail-band mass. -/
theorem expectation_preservation (D : Model Ω S) (s : S) (N : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, horizonCredit D N F x ∂D.posterior s =
      (∫⁻ x, F x ∂D.posterior s) + D.posterior s (tailBand D N) := by
  unfold horizonCredit
  rw [lintegral_add_left hF, lintegral_indicator_const (measurableSet_tailBand D N), one_mul]

/-- Finite real values admit an upper-bracket horizon with arbitrarily small credit cost. -/
theorem exists_horizon (D : Model Ω S) (s : S) (start : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, start ≤ N ∧ (∫⁻ x, horizonCredit D N F x ∂D.posterior s) ≤
      (∫⁻ x, F x ∂D.posterior s) + δ := by
  have herror : ∀ᵐ x ∂D.posterior s,
      Tendsto (fun n => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    ae_of_all _ fun _ => tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hne : ∀ᵐ x ∂D.posterior s, tailDistance D x ≠ 0 :=
    ae_of_all _ fun x => (tailDistance_pos D x).ne'
  obtain ⟨N, hstart, hN⟩ := LatentComparisonUncertainty.exists_small_mass_ge
    (D.posterior s) (measurable_tailDistance D) measurable_const
    (fun _ => measurable_const) herror hne start hδ
  refine ⟨N, hstart, ?_⟩
  rw [expectation_preservation D s N F hF]
  exact add_le_add le_rfl hN.le

/-- Failure at the selected doubling horizon consumes a whole unit of auxiliary credit. -/
theorem unresolved_mem_tailBand (D : Model Ω S) (degree N : ℕ) (hdegree : degree ≠ 0)
    (x : Ω) (h : ((2 : ℝ) ^ N) ^ degree ≤ D.value x) : x ∈ tailBand D N := by
  have hpow : (2 : ℝ) ^ N ≤ ((2 : ℝ) ^ N) ^ degree :=
    le_self_pow₀ (one_le_pow₀ (by norm_num)) hdegree
  have hbound : (2 : ℝ) ^ N ≤ 1 + |D.value x| :=
    (hpow.trans h).trans (by linarith [le_abs_self (D.value x)])
  have hd : tailDistance D x ≤ (1 / 2 : ℝ) ^ N := by
    rw [one_div_pow]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hbound
  simpa only [tailBand, LatentComparisonUncertainty.band, mem_ofPred_eq, sub_zero,
    abs_of_pos (tailDistance_pos D x)] using hd

end

end SampLib.LatentReal.Root
