module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # Beta–gamma multiplication

The change of variables `(x,y) = (su,s(1-u))` separates the sum from its
proportion. Its Jacobian `s` turns two gamma densities into a beta density and
the gamma density of the sum. Marginalizing the second gamma factor proves the
product law, with arbitrary nonnegative extended-real continuation credits.
-/

open Set MeasureTheory ProbabilityTheory Real
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.BetaExponentialProduct

noncomputable section

private theorem measurable_gamma (a r : ℝ) : Measurable (gammaPDF a r) :=
  ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)

private theorem measurable_beta (a b : ℝ) : Measurable (betaPDF a b) :=
  ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)

/-- The scalar Jacobian identity, on the positive sum and proportion domains. -/
theorem density_factor_real (a b r s u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (hs : 0 < s) (hu : u ∈ Ioo (0 : ℝ) 1) :
    s * gammaPDFReal a r (s * u) * gammaPDFReal b r (s * (1 - u)) =
      betaPDFReal a b u * gammaPDFReal (a + b) r s := by
  have hΓa := Gamma_pos_of_pos ha
  have hΓb := Gamma_pos_of_pos hb
  have hΓab := Gamma_pos_of_pos (add_pos ha hb)
  have hu' : 0 < 1 - u := sub_pos.mpr hu.2
  have he : exp (-(r * (s * u))) * exp (-(r * (s * (1 - u)))) = exp (-(r * s)) := by
    rw [← exp_add]
    congr 1
    ring
  simp only [gammaPDFReal, betaPDFReal, ite_eq_left (mul_pos hs hu.1).le,
    ite_eq_left (mul_pos hs hu').le, ite_eq_left hs.le, ite_eq_left (show 0 < u ∧ u < 1 from hu)]
  rw [mul_rpow hs.le hu.1.le, mul_rpow hs.le hu'.le]
  calc
    _ = (s * (r ^ a / Gamma a) * (r ^ b / Gamma b) * s ^ (a - 1) * s ^ (b - 1) *
        u ^ (a - 1) * (1 - u) ^ (b - 1)) *
          (exp (-(r * (s * u))) * exp (-(r * (s * (1 - u))))) := by ring
    _ = _ := by
      rw [he]
      unfold beta
      rw [rpow_sub hs, rpow_sub hs, rpow_sub hs, rpow_one,
        rpow_add hr, rpow_add hs]
      field_simp [hΓa.ne', hΓb.ne', hΓab.ne', hs.ne']

/-- The density identity holds almost everywhere, including shapes singular at zero. -/
theorem density_factor (a b r s : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (hs : 0 < s) :
    (fun u => ofReal s * gammaPDF a r (s * u) *
      gammaPDF b r (s * (1 - u))) =ᵐ[volume]
      (fun u => betaPDF a b u * gammaPDF (a + b) r s) := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ)] with u hu0 hu1
  by_cases hlo : 0 < u
  · by_cases hhi : u < 1
    · change ofReal s * ofReal (gammaPDFReal a r (s * u)) *
        ofReal (gammaPDFReal b r (s * (1 - u))) =
          ofReal (betaPDFReal a b u) * ofReal (gammaPDFReal (a + b) r s)
      rw [← ENNReal.ofReal_mul hs.le,
        ← ENNReal.ofReal_mul (mul_nonneg hs.le (gammaPDFReal_nonneg ha hr _)),
        ← ENNReal.ofReal_mul (betaPDFReal_pos hlo hhi ha hb).le]
      exact congrArg ofReal (density_factor_real a b r s u ha hb hr hs ⟨hlo, hhi⟩)
    · have hu : 1 < u := lt_of_le_of_ne (not_lt.mp hhi) hu1.symm
      rw [gammaPDF_of_neg (mul_neg_of_pos_of_neg hs (sub_neg.mpr hu)),
        betaPDF_eq_zero_of_one_le hu.le, mul_zero, zero_mul]
  · have hu : u < 0 := lt_of_le_of_ne (not_lt.mp hlo) hu0
    rw [gammaPDF_of_neg (mul_neg_of_pos_of_neg hs hu),
      betaPDF_eq_zero_of_nonpos hu.le, mul_zero, zero_mul, zero_mul]

/-- Lebesgue scaling, retaining the Jacobian outside an arbitrary ENNReal integral. -/
theorem lintegral_scale (s : ℝ) (hs : 0 < s) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x) = ofReal s * ∫⁻ u, f (s * u) := by
  calc
    _ = ∫⁻ x, f x ∂(ofReal |s| • Measure.map (fun u : ℝ => s * u) volume) := by
      rw [Real.smul_map_volume_mul_left hs.ne']
    _ = _ := by
      rw [lintegral_smul_measure, lintegral_map hf (measurable_const_mul s),
        abs_of_pos hs, smul_eq_mul]

/-- Sum and proportion separate the joint gamma density, for arbitrary joint credits. -/
theorem gamma_pair_transform (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (G : ℝ × ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x, ∫⁻ y, gammaPDF a r x * gammaPDF b r y * G (x, y)) =
      ∫⁻ s, ∫⁻ u, betaPDF a b u * gammaPDF (a + b) r s *
        G (s * u, s * (1 - u)) := by
  have hK : Measurable (fun z : ℝ × ℝ =>
      gammaPDF a r z.1 * gammaPDF b r (z.2 - z.1) * G (z.1, z.2 - z.1)) :=
    ((measurable_gamma a r).comp measurable_fst).mul
      ((measurable_gamma b r).comp (measurable_snd.sub measurable_fst)) |>.mul
      (hG.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst)))
  have hKfix (s : ℝ) : Measurable (fun x =>
      gammaPDF a r x * gammaPDF b r (s - x) * G (x, s - x)) :=
    (measurable_gamma a r).mul
      ((measurable_gamma b r).comp (measurable_const.sub measurable_id)) |>.mul
      (hG.comp (measurable_id.prodMk (measurable_const.sub measurable_id)))
  calc
    _ = ∫⁻ x, ∫⁻ s, gammaPDF a r x * gammaPDF b r (s - x) * G (x, s - x) := by
      apply lintegral_congr
      intro x
      simpa only [sub_eq_add_neg] using
        (lintegral_add_right_eq_self
          (fun y => gammaPDF a r x * gammaPDF b r y * G (x, y)) (-x)).symm
    _ = ∫⁻ s, ∫⁻ x, gammaPDF a r x * gammaPDF b r (s - x) * G (x, s - x) :=
      lintegral_lintegral_swap hK.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with s hs
      rcases lt_or_gt_of_ne hs with hs | hs
      · have hz (x : ℝ) : gammaPDF a r x * gammaPDF b r (s - x) = 0 := by
          rcases lt_or_ge x 0 with hx | hx
          · rw [gammaPDF_of_neg hx, zero_mul]
          · rw [gammaPDF_of_neg (by linarith : s - x < 0), mul_zero]
        simp only [hz, gammaPDF_of_neg hs, zero_mul, mul_zero, lintegral_zero]
      · have hscaled : Measurable (fun u => gammaPDF a r (s * u) *
            gammaPDF b r (s - s * u) * G (s * u, s - s * u)) :=
          (hKfix s).comp (measurable_const_mul s)
        rw [lintegral_scale s hs _ (hKfix s), ← lintegral_const_mul _ hscaled]
        apply lintegral_congr_ae
        filter_upwards [density_factor a b r s ha hb hr hs] with u hu
        rw [show s - s * u = s * (1 - u) by ring]
        calc
          _ = (ofReal s * gammaPDF a r (s * u) * gammaPDF b r (s * (1 - u))) *
              G (s * u, s * (1 - u)) := by ring
          _ = _ := by rw [hu]

/-- Multiplying an independent beta proportion by a gamma sum keeps the first shape. -/
theorem expectation_gamma (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, ∫⁻ s, F (u * s) ∂gammaMeasure (a + b) r ∂betaMeasure a b) =
      ∫⁻ x, F x ∂gammaMeasure a r := by
  let := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hIF : Measurable (fun u => ∫⁻ s, F (u * s) ∂gammaMeasure (a + b) r) :=
    (hF.comp (measurable_fst.mul measurable_snd)).lintegral_prod_right'
  have hFx (u : ℝ) : Measurable (fun s => F (u * s)) :=
    hF.comp (measurable_const.mul measurable_id)
  have hterm (u : ℝ) : Measurable (fun s => gammaPDF (a + b) r s * F (u * s)) :=
    (measurable_gamma (a + b) r).mul (hFx u)
  have hpair := gamma_pair_transform a b r ha hb hr
    (fun z => F z.1) (hF.comp measurable_fst)
  have hboth : Measurable (fun z : ℝ × ℝ =>
      betaPDF a b z.1 * gammaPDF (a + b) r z.2 * F (z.1 * z.2)) :=
    ((measurable_beta a b).comp measurable_fst).mul
      ((measurable_gamma (a + b) r).comp measurable_snd) |>.mul
      (hF.comp (measurable_fst.mul measurable_snd))
  calc
    _ = ∫⁻ u, betaPDF a b u *
        (∫⁻ s, gammaPDF (a + b) r s * F (u * s)) := by
      rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_beta a b) hIF]
      apply lintegral_congr
      intro u
      change betaPDF a b u * (∫⁻ s, F (u * s) ∂gammaMeasure (a + b) r) = _
      rw [gammaMeasure, lintegral_withDensity_eq_lintegral_mul _
        (measurable_gamma (a + b) r) (hFx u)]
      rfl
    _ = ∫⁻ u, ∫⁻ s, betaPDF a b u * gammaPDF (a + b) r s * F (u * s) := by
      apply lintegral_congr
      intro u
      rw [← lintegral_const_mul _ (hterm u)]
      apply lintegral_congr
      intro s
      ring
    _ = ∫⁻ s, ∫⁻ u, betaPDF a b u * gammaPDF (a + b) r s * F (u * s) :=
      lintegral_lintegral_swap hboth.aemeasurable
    _ = ∫⁻ s, ∫⁻ u, betaPDF a b u * gammaPDF (a + b) r s * F (s * u) := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro u
      rw [mul_comm u s]
    _ = ∫⁻ x, ∫⁻ y, gammaPDF a r x * gammaPDF b r y * F x := hpair.symm
    _ = ∫⁻ x, gammaPDF a r x * F x := by
      apply lintegral_congr
      intro x
      calc
        _ = (gammaPDF a r x * F x) * ∫⁻ y, gammaPDF b r y := by
          rw [← lintegral_const_mul _ (measurable_gamma b r)]
          apply lintegral_congr
          intro y
          ring
        _ = _ := by rw [lintegral_gammaPDF_eq_one hb hr, mul_one]
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ (measurable_gamma a r) hF).symm

/-- The canonical beta–gamma product identity, at every pair of positive shapes. -/
theorem beta_mul_gamma (a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((betaMeasure a b).prod (gammaMeasure (a + b) r)).map
      (fun z : ℝ × ℝ => z.1 * z.2) = gammaMeasure a r := by
  let := isProbabilityMeasureBeta ha hb
  let := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hmul : Measurable (fun z : ℝ × ℝ => z.1 * z.2) :=
    measurable_fst.mul measurable_snd
  rw [lintegral_map hF hmul]
  have hprod : Measurable (fun z : ℝ × ℝ => F (z.1 * z.2)) :=
    hF.comp (measurable_fst.mul measurable_snd)
  exact (lintegral_prod _ hprod.aemeasurable).trans
    (expectation_gamma a b r ha hb hr F hF)

/-- A complementary-shape beta proportion turns an exponential into a fractional gamma. -/
theorem beta_mul_exponential (a r : ℝ) (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r) :
    ((betaMeasure a (1 - a)).prod (expMeasure r)).map
      (fun z : ℝ × ℝ => z.1 * z.2) = gammaMeasure a r := by
  have hab : a + (1 - a) = 1 := by ring
  simpa only [hab, expMeasure] using beta_mul_gamma a (1 - a) r ha (sub_pos.mpr ha1) hr

/-- The fractional-shape sampler's expectation identity, including infinite credits. -/
theorem expectation (a r : ℝ) (ha : 0 < a) (ha1 : a < 1) (hr : 0 < r)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, ∫⁻ s, F (u * s) ∂expMeasure r ∂betaMeasure a (1 - a)) =
      ∫⁻ x, F x ∂gammaMeasure a r := by
  have hab : a + (1 - a) = 1 := by ring
  simpa only [hab, expMeasure] using
    expectation_gamma a (1 - a) r ha (sub_pos.mpr ha1) hr F hF

end

end SampLib.BetaExponentialProduct
