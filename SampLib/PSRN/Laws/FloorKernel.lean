import SampLib.Latent.LatentMeasuredError
import SampLib.PSRN.Laws.FloorUncertainty

/-! # Joint continuation credits for exact integer-grid observations -/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SampLib.LatentReal.Floor

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

def output (D : Model Ω S) (scale : ℤ) (x : Ω) : ℤ := ⌊D.value x * scale⌋

@[fun_prop] theorem measurable_output (D : Model Ω S) (scale : ℤ) :
    Measurable (output D scale) := by
  exact (D.measurable_value.mul_const _).floor

/-- A sufficient termination domain excludes the scaled integer-grid boundaries. -/
def AvoidsGrid (D : Model Ω S) (scale : ℤ) (s : S) : Prop :=
  ∀ᵐ x ∂D.posterior s, D.value x * scale ≠ (output D scale x : ℝ)

def band (D : Model Ω S) (scale : ℤ) (n : ℕ) : Set Ω :=
  LatentComparisonUncertainty.band
    (fun x => LatentFloorUncertainty.margin (D.value x * scale)) (fun _ => 0)
    (fun n x => D.error n x * scale) n

theorem measurableSet_band (D : Model Ω S) (hD : D.MeasurableError) (scale : ℤ) (n : ℕ) :
    MeasurableSet (band D scale n) := by
  apply LatentComparisonUncertainty.measurableSet_band
  · exact LatentFloorUncertainty.measurable_margin.comp (D.measurable_value.mul_const _)
  · exact measurable_const
  · exact fun n => (hD n).mul_const _

def outputCredit (D : Model Ω S) (scale : ℤ) (G : ℤ → Ω → ℝ≥0∞) (x : Ω) : ℝ≥0∞ :=
  G (output D scale x) x

def horizonCredit (D : Model Ω S) (scale : ℤ) (N : ℕ) (G : ℤ → Ω → ℝ≥0∞)
    (x : Ω) : ℝ≥0∞ :=
  outputCredit D scale G x + (band D scale N).indicator (fun _ => 1) x

theorem measurable_outputCredit (D : Model Ω S) (scale : ℤ) (G : ℤ → Ω → ℝ≥0∞)
    (hG : ∀ z, Measurable (G z)) : Measurable (outputCredit D scale G) :=
  (measurable_from_prod_countable_right (f := fun p : ℤ × Ω => G p.1 p.2) hG).comp
    ((measurable_output D scale).prodMk measurable_id)

theorem measurable_horizonCredit (D : Model Ω S) (hD : D.MeasurableError)
    (scale : ℤ) (N : ℕ) (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    Measurable (horizonCredit D scale N G) :=
  (measurable_outputCredit D scale G hG).add
    (measurable_const.indicator (measurableSet_band D hD scale N))

/-- Auxiliary credit costs the unresolved grid band's mass, regardless of output-credit size. -/
theorem expectation_preservation (D : Model Ω S) (s : S) (hD : D.MeasurableError)
    (scale : ℤ) (N : ℕ) (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    ∫⁻ x, horizonCredit D scale N G x ∂D.posterior s =
      (∫⁻ x, outputCredit D scale G x ∂D.posterior s) + D.posterior s (band D scale N) := by
  unfold horizonCredit
  rw [lintegral_add_left (measurable_outputCredit D scale G hG),
    lintegral_indicator_const (measurableSet_band D hD scale N), one_mul]

/-- Off the integer grid, vanishing enclosure errors give a finite proof horizon. -/
theorem exists_horizon (D : Model Ω S) (s : S) (hD : D.MeasurableError)
    (scale : ℤ) (hgrid : AvoidsGrid D scale s) (start : ℕ)
    (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, start ≤ N ∧ (∫⁻ x, horizonCredit D scale N G x ∂D.posterior s) ≤
      (∫⁻ x, outputCredit D scale G x ∂D.posterior s) + δ := by
  have herror : ∀ᵐ x ∂D.posterior s,
      Tendsto (fun n => D.error n x * (scale : ℝ)) atTop (𝓝 0) :=
    (D.error_tendsto s).mono fun _ hx => by simpa using hx.mul_const (scale : ℝ)
  have hne : ∀ᵐ x ∂D.posterior s,
      LatentFloorUncertainty.margin (D.value x * scale) ≠ 0 :=
    hgrid.mono fun _ hx => (LatentFloorUncertainty.margin_pos hx).ne'
  obtain ⟨N, hstart, hN⟩ := LatentComparisonUncertainty.exists_small_mass_ge
    (D.posterior s)
    (LatentFloorUncertainty.measurable_margin.comp (D.measurable_value.mul_const _))
    measurable_const (fun n => (hD n).mul_const _) herror hne start hδ
  refine ⟨N, hstart, ?_⟩
  rw [expectation_preservation D s hD scale N G hG]
  exact add_le_add le_rfl hN.le

/-- Matching endpoint quotients determine the integer under the refined posterior. -/
theorem resolves (D : Model Ω S) (s : S) (n : ℕ) (scale : ℤ) (hscale : 0 ≤ scale)
    (I : RationalInterval) (hI : D.Encloses s n I)
    (h : I.lowerFloor scale = I.upperFloor scale) :
    ∀ᵐ x ∂D.posterior s, output D scale x = I.lowerFloor scale :=
  hI.mono fun _ hx => I.floor_eq_of_resolved hx.1 hscale h

theorem return_credit (D : Model Ω S) (s : S) (scale : ℤ) (N : ℕ)
    (G : ℤ → Ω → ℝ≥0∞) (z : ℤ)
    (h : ∀ᵐ x ∂D.posterior s, output D scale x = z) :
    (∫⁻ x, G z x ∂D.posterior s) ≤ ∫⁻ x, horizonCredit D scale N G x ∂D.posterior s :=
  lintegral_mono_ae (h.mono fun x hx => by simp [horizonCredit, outputCredit, hx])

/-- An unresolved enclosure at the proof horizon owns a whole credit and is impossible. -/
theorem unresolved_credit (D : Model Ω S) (s : S) (scale : ℤ) (hscale : 0 ≤ scale)
    (N : ℕ) (G : ℤ → Ω → ℝ≥0∞) (I : RationalInterval) (hI : D.Encloses s N I)
    (h : I.lowerFloor scale ≠ I.upperFloor scale) :
    1 ≤ ∫⁻ x, horizonCredit D scale N G x ∂D.posterior s := by
  calc
    1 = ∫⁻ _ : Ω, 1 ∂D.posterior s := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hI] with x hx
      have hmargin := (I.unresolved_margin_le hx.1 hscale h).trans
        (mul_le_mul_of_nonneg_right hx.2 (by exact_mod_cast hscale))
      have hband : x ∈ band D scale N := by
        simpa only [band, LatentComparisonUncertainty.band, mem_ofPred_eq, sub_zero,
          abs_of_nonneg (LatentFloorUncertainty.margin_nonneg _)] using hmargin
      simp [horizonCredit, hband]

end

end SampLib.LatentReal.Floor
