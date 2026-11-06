import SampLib.Latent.Laws.MeasuredError
import SampLib.PSRN.Laws.IntervalComparison

/-! # Joint credits for exact comparison of two shared latent views

Only overlap at one fixed horizon needs auxiliary credit. Its initial expectation
is the mass of a shrinking uncertainty band, even when the views are dependent.
-/

open MeasureTheory Set
open scoped ENNReal

namespace SampLib.LatentReal.Less

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The order event concerns two projections of the same latent world. -/
def event (left right : Model Ω S) : Set Ω := {x | left.value x < right.value x}

noncomputable instance eventDecidable (left right : Model Ω S) :
    DecidablePred (· ∈ event left right) := fun _ => Classical.propDecidable _

theorem measurableSet_event (left right : Model Ω S) : MeasurableSet (event left right) :=
  measurableSet_lt left.measurable_value right.measurable_value

def outputCredit (left right : Model Ω S) (G : Bool → Ω → ℝ≥0∞) (x : Ω) : ℝ≥0∞ :=
  G (decide (x ∈ event left right)) x

def horizonCredit (left right : Model Ω S) (N : ℕ) (G : Bool → Ω → ℝ≥0∞)
    (x : Ω) : ℝ≥0∞ :=
  outputCredit left right G x + (Model.comparisonBand left right N).indicator (fun _ => 1) x

theorem measurable_outputCredit (left right : Model Ω S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) : Measurable (outputCredit left right G) := by
  have heq : outputCredit left right G =
      fun x => if x ∈ event left right then G true x else G false x := by
    funext x
    by_cases hx : x ∈ event left right <;> simp [outputCredit, hx]
  rw [heq]
  exact Measurable.ite (measurableSet_event left right) (hG true) (hG false)

theorem measurable_horizonCredit (left right : Model Ω S)
    (hl : left.MeasurableError) (hr : right.MeasurableError) (N : ℕ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    Measurable (horizonCredit left right N G) :=
  (measurable_outputCredit left right G hG).add
    (measurable_const.indicator (Model.measurableSet_comparisonBand left right hl hr N))

/-- The extra credit costs exactly the unresolved band's mass under the current joint posterior. -/
theorem expectation_preservation (left right : Model Ω S) (s : S)
    (hl : left.MeasurableError) (hr : right.MeasurableError) (N : ℕ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    ∫⁻ x, horizonCredit left right N G x ∂left.posterior s =
      (∫⁻ x, outputCredit left right G x ∂left.posterior s) +
        left.posterior s (Model.comparisonBand left right N) := by
  unfold horizonCredit
  rw [lintegral_add_left (measurable_outputCredit left right G hG),
    lintegral_indicator_const (Model.measurableSet_comparisonBand left right hl hr N), one_mul]

/-- Almost-surely distinct views admit one finite proof horizon after any starting precision. -/
theorem exists_horizon (left right : Model Ω S) (hworld : left.SameWorld right)
    (hl : left.MeasurableError) (hr : right.MeasurableError) (s : S)
    (hne : ∀ᵐ x ∂left.posterior s, left.value x ≠ right.value x) (start : ℕ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b))
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ N, start ≤ N ∧ (∫⁻ x, horizonCredit left right N G x ∂left.posterior s) ≤
      (∫⁻ x, outputCredit left right G x ∂left.posterior s) + δ := by
  obtain ⟨N, hstart, hN⟩ := hworld.exists_small_comparison_band hl hr s hne start hδ
  refine ⟨N, hstart, ?_⟩
  rw [expectation_preservation left right s hl hr N G hG]
  exact add_le_add le_rfl hN.le

/-- Sequential reads share one posterior; the right enclosure is interpreted in the left world. -/
theorem right_encloses (left right : Model Ω S) (hworld : left.SameWorld right)
    {s : S} {n : ℕ} {I : RationalInterval} (hI : right.Encloses s n I) :
    ∀ᵐ x ∂left.posterior s,
      I.Contains (right.value x) ∧ I.width ≤ right.error n x := by
  simpa only [Model.Encloses, RationalInterval.width, hworld.posterior_eq s] using hI

theorem true_resolves (left right : Model Ω S) (hworld : left.SameWorld right)
    {s : S} {n : ℕ} {I J : RationalInterval}
    (hI : left.Encloses s n I) (hJ : right.Encloses s n J)
    (h : I.upper * J.denominator < J.lower * I.denominator) :
    ∀ᵐ x ∂left.posterior s, decide (x ∈ event left right) = true := by
  filter_upwards [hI, right_encloses left right hworld hJ] with x hx hy
  exact decide_eq_true (I.lt_of_strict_test J hx.1 hy.1 h)

theorem false_resolves (left right : Model Ω S) (hworld : left.SameWorld right)
    {s : S} {n : ℕ} {I J : RationalInterval}
    (hI : left.Encloses s n I) (hJ : right.Encloses s n J)
    (h : J.upper * I.denominator ≤ I.lower * J.denominator) :
    ∀ᵐ x ∂left.posterior s, decide (x ∈ event left right) = false := by
  filter_upwards [hI, right_encloses left right hworld hJ] with x hx hy
  exact decide_eq_false (I.not_lt_of_reverse_test J hx.1 hy.1 h)

/-- A settled comparison returns the full joint continuation, including infinite credits. -/
theorem return_credit (left right : Model Ω S) (s : S) (N : ℕ)
    (G : Bool → Ω → ℝ≥0∞) (b : Bool)
    (h : ∀ᵐ x ∂left.posterior s, decide (x ∈ event left right) = b) :
    (∫⁻ x, G b x ∂left.posterior s) ≤ ∫⁻ x, horizonCredit left right N G x ∂left.posterior s :=
  lintegral_mono_ae (h.mono fun x hx => by simp [horizonCredit, outputCredit, hx])

/-- Overlap at the selected horizon owns one whole credit and is therefore impossible. -/
theorem unresolved_credit (left right : Model Ω S) (hworld : left.SameWorld right)
    (s : S) (N : ℕ) (G : Bool → Ω → ℝ≥0∞) (I J : RationalInterval)
    (hI : left.Encloses s N I) (hJ : right.Encloses s N J)
    (hstrict : ¬I.upper * J.denominator < J.lower * I.denominator)
    (hreverse : ¬J.upper * I.denominator ≤ I.lower * J.denominator) :
    1 ≤ ∫⁻ x, horizonCredit left right N G x ∂left.posterior s := by
  calc
    1 = ∫⁻ _ : Ω, 1 ∂left.posterior s := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hI, right_encloses left right hworld hJ] with x hx hy
      have hband : x ∈ Model.comparisonBand left right N :=
        I.unresolved_error_le J hx.1 hy.1 hstrict hreverse hx.2 hy.2
      simp [horizonCredit, hband]

end

end SampLib.LatentReal.Less
