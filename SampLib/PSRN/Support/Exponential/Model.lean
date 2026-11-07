import SampLib.Latent.LatentDigitModel
import SampLib.PSRN.Laws.ExponentialDigitLaw
import SampLib.PSRN.Laws.ExponentialWholeFraction
import SampLib.PSRN.Support.Arithmetic.RationalTranslate

/-! # A deferred exponential's whole and fractional posterior

Before allocation the whole and fraction are independent. Once the whole is
sampled, its exact integer is retained while fraction reads condition the same
canonical digit stream. All subsequent states refine this one joint world.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentExponential

noncomputable section

open ExponentialDigits

abbrev DigitState (rate : ℝ) := LatentDigits.State (fraction rate) digits
abbrev State (rate : ℝ) := Option (ℕ × DigitState rate)

def initial (rate : ℝ) : State rate := none

/-- The whole coordinate is fixed after its first draw; digit reads refine the fraction. -/
def posterior (rate : ℝ) (hrate : 0 < rate) : State rate → Measure (ℕ × ℝ)
  | none => (ProbabilityTheory.geometricMeasure (wholeBias rate hrate)).prod (fraction rate)
  | some (k, p) => (Measure.dirac k).prod (DigitPosterior.law (fraction rate) digits p.val)

theorem probability (rate : ℝ) (hrate : 0 < rate) (s : State rate) :
    IsProbabilityMeasure (posterior rate hrate s) := by
  let := fraction_probability rate hrate
  cases s with
  | none => unfold posterior; infer_instance
  | some s =>
    let := DigitPosterior.probability (fraction rate) digits s.2.val s.2.property
    unfold posterior
    infer_instance

def refines {rate : ℝ} : State rate → State rate → Prop
  | none, _ => True
  | some _, none => False
  | some (k, p), some (l, q) => k = l ∧ p.val <+: q.val

private theorem refines_refl {rate : ℝ} (s : State rate) : refines s s := by
  cases s with
  | none => trivial
  | some s => exact ⟨rfl, List.prefix_refl _⟩

private theorem refines_trans {rate : ℝ} {s t u : State rate}
    (hst : refines s t) (htu : refines t u) : refines s u := by
  cases s with
  | none => trivial
  | some s =>
    cases t with
    | none => exact False.elim hst
    | some t =>
      cases u with
      | none => exact False.elim htu
      | some u => exact ⟨hst.1.trans htu.1, hst.2.trans htu.2⟩

private theorem geometric_atom_pos (rate : ℝ) (hrate : 0 < rate) (k : ℕ) :
    0 < ProbabilityTheory.geometricMeasure (wholeBias rate hrate) {k} := by
  have hzero : wholeBias rate hrate ≠ 0 := by
    intro h
    have hp := wholeBias_pos rate hrate
    simp only [h, Set.Icc.coe_zero, lt_self_iff_false] at hp
  have hone : wholeBias rate hrate ≠ 1 := by
    intro h
    have he := congrArg (fun p : unitInterval => (p : ℝ)) h
    have hp := Real.exp_pos (-rate)
    simp only [wholeBias, Set.Icc.coe_one] at he
    linarith
  rw [ProbabilityTheory.geometricMeasure_singleton hzero]
  exact ENNReal.ofReal_pos.mpr (ProbabilityTheory.geometricMeasure_pos hzero hone k)

private theorem dirac_geometric_ac (rate : ℝ) (hrate : 0 < rate) (k : ℕ) :
    Measure.dirac k ≪ ProbabilityTheory.geometricMeasure (wholeBias rate hrate) := by
  intro A hA
  by_cases hk : k ∈ A
  · have hm : ProbabilityTheory.geometricMeasure (wholeBias rate hrate) {k} ≤
        ProbabilityTheory.geometricMeasure (wholeBias rate hrate) A :=
      measure_mono (Set.singleton_subset_iff.mpr hk : {k} ⊆ A)
    rw [hA] at hm
    exact False.elim ((not_le_of_gt (geometric_atom_pos rate hrate k)) hm)
  · simp [hk]

theorem posterior_refines (rate : ℝ) (hrate : 0 < rate) {s t : State rate}
    (hst : refines s t) : posterior rate hrate t ≪ posterior rate hrate s := by
  let := fraction_probability rate hrate
  cases s with
  | none =>
    cases t with
    | none => exact Measure.AbsolutelyContinuous.rfl
    | some t =>
      exact (dirac_geometric_ac rate hrate t.1).prod ProbabilityTheory.cond_absolutelyContinuous
  | some s =>
    cases t with
    | none => exact False.elim hst
    | some t =>
      change s.1 = t.1 ∧ s.2.val <+: t.2.val at hst
      rcases hst with ⟨hk, hp⟩
      dsimp only [posterior]
      rw [← hk]
      exact Measure.AbsolutelyContinuous.rfl.prod
        (DigitPosterior.law_refines (fraction rate) measurable_digits hp)

/-- One joint world for the whole part and all progressively revealed fractional digits. -/
def model (rate : ℝ) (hrate : 0 < rate) : LatentReal.Model (ℕ × ℝ) (State rate) where
  posterior := posterior rate hrate
  probability := probability rate hrate
  value z := (z.1 : ℝ) + DigitPosterior.value (digits z.2)
  measurable_value :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp measurable_fst).add
      ((DigitPosterior.measurable_value measurable_digits).comp measurable_snd)
  refines := refines
  refines_refl := refines_refl
  refines_trans := refines_trans
  absolutelyContinuous := posterior_refines rate hrate
  error n _ := (2 ^ n : ℝ)⁻¹
  error_tendsto _ := Filter.Eventually.of_forall fun _ =>
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

theorem measurable_error (rate : ℝ) (hrate : 0 < rate) :
    (model rate hrate).MeasurableError := fun _ => measurable_const

@[simp] theorem posterior_initial (rate : ℝ) (hrate : 0 < rate) :
    (model rate hrate).posterior (initial rate) =
      (ProbabilityTheory.geometricMeasure (wholeBias rate hrate)).prod (fraction rate) := rfl

@[simp] theorem posterior_some (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p : DigitState rate) :
    (model rate hrate).posterior (some (k, p)) =
      (Measure.dirac k).prod (DigitPosterior.law (fraction rate) digits p.val) := rfl

theorem initial_refines (rate : ℝ) (hrate : 0 < rate) (s : State rate) :
    (model rate hrate).refines (initial rate) s := by trivial

/-- Initial joint credits allocate the independent whole and fractional worlds. -/
theorem initial_expectation (rate : ℝ) (hrate : 0 < rate) (F : ℕ × ℝ → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ z, F z ∂(model rate hrate).posterior (initial rate)) =
      ∫⁻ k, ∫⁻ x, F (k, x) ∂fraction rate
        ∂ProbabilityTheory.geometricMeasure (wholeBias rate hrate) := by
  let := fraction_probability rate hrate
  rw [posterior_initial, lintegral_prod _ hF.aemeasurable]

/-- Once the whole is observed, every continuation keeps that exact joint coordinate. -/
theorem some_expectation (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p : DigitState rate)
    (F : ℕ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂(model rate hrate).posterior (some (k, p))) =
      ∫⁻ x, F (k, x) ∂DigitPosterior.law (fraction rate) digits p.val := by
  let := fraction_probability rate hrate
  let := DigitPosterior.probability (fraction rate) digits p.val p.property
  rw [posterior_some, lintegral_prod _ hF.aemeasurable, lintegral_dirac]

/-- The initial represented real has the canonical exponential distribution. -/
theorem initial_law (rate : ℝ) (hrate : 0 < rate) :
    (model rate hrate).law (initial rate) = ProbabilityTheory.expMeasure rate := by
  let := fraction_probability rate hrate
  apply Measure.ext_of_lintegral
  intro F hF
  rw [LatentReal.Model.law, lintegral_map hF (model rate hrate).measurable_value]
  change (∫⁻ z, F ((z.1 : ℝ) + DigitPosterior.value (digits z.2))
    ∂(ProbabilityTheory.geometricMeasure (wholeBias rate hrate)).prod (fraction rate)) = _
  have hMF : Measurable (fun z : ℕ × ℝ =>
      F ((z.1 : ℝ) + DigitPosterior.value (digits z.2))) :=
    hF.comp (model rate hrate).measurable_value
  rw [lintegral_prod _ hMF.aemeasurable]
  calc
    _ = ∫⁻ k, ∫⁻ x, F ((k : ℝ) + x) ∂fraction rate
        ∂ProbabilityTheory.geometricMeasure (wholeBias rate hrate) := by
      apply lintegral_congr
      intro k
      apply lintegral_congr_ae
      filter_upwards [fraction_support rate] with x hx
      rw [value_digits hx]
    _ = _ := ExponentialDigits.expectation rate hrate F hF

end

end SampLib.LatentExponential

open MeasureTheory

namespace SampLib.LatentExponential

noncomputable section

open ExponentialDigits

/-- Once the integer is fixed, refinement is exactly extension of the fractional prefix. -/
theorem refines_some (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p q : DigitState rate) :
    (model rate hrate).refines (some (k, p)) (some (k, q)) ↔ p.val <+: q.val := by
  change (k = k ∧ p.val <+: q.val) ↔ p.val <+: q.val
  simp

/-- A translated fractional enclosure is an enclosure of the same exponential world. -/
theorem encloses_some (rate : ℝ) (hrate : 0 < rate) (k : ℕ) (p : DigitState rate)
    (n : ℕ) (I : LatentReal.RationalInterval)
    (hI : ((@LatentDigits.model ℝ _ (fraction rate) (fraction_probability rate hrate)
      digits measurable_digits).translate (k : ℝ)).Encloses p n I) :
    (model rate hrate).Encloses (some (k, p)) n I := by
  let := fraction_probability rate hrate
  let := DigitPosterior.probability (fraction rate) digits p.val p.property
  change ∀ᵐ x ∂DigitPosterior.law (fraction rate) digits p.val,
    I.Contains ((k : ℝ) + DigitPosterior.value (digits x)) ∧
      I.upperReal - I.lowerReal ≤ (2 ^ n : ℝ)⁻¹ at hI
  change ∀ᵐ z ∂(Measure.dirac k).prod (DigitPosterior.law (fraction rate) digits p.val),
    I.Contains ((z.1 : ℝ) + DigitPosterior.value (digits z.2)) ∧
      I.upperReal - I.lowerReal ≤ (2 ^ n : ℝ)⁻¹
  have hfraction := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.dirac k) (ν := DigitPosterior.law (fraction rate) digits p.val)).ae hI
  have hk : ∀ᵐ j ∂Measure.dirac k, j = k := by simp [ae_dirac_eq]
  have hwhole : ∀ᵐ z ∂(Measure.dirac k).prod (DigitPosterior.law (fraction rate) digits p.val),
      z.1 = k := (Measure.quasiMeasurePreserving_fst
        (μ := Measure.dirac k) (ν := DigitPosterior.law (fraction rate) digits p.val)).ae hk
  filter_upwards [hfraction, hwhole] with z hz hk
  simpa only [hk] using hz

end

end SampLib.LatentExponential
