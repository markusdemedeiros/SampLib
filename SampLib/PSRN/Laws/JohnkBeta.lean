module

public import SampLib.PSRN.Laws.BetaExponentialProduct

@[expose] public section

/-! # Johnk's beta rejection law

Independent Beta(a,1) and Beta(b,1) proposals are accepted when their sum is
less than one. Sum and proportion coordinates separate the accepted density:
the radial integral contributes 1/(a+b), leaving the canonical Beta(a,b) law.
-/

open Set MeasureTheory ProbabilityTheory Real
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.JohnkBeta

noncomputable section

private theorem measurable_beta (a b : ℝ) : Measurable (betaPDF a b) :=
  ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)

/-- The power proposal's normalizing constant. -/
theorem beta_one (a : ℝ) (ha : 0 < a) : beta a 1 = 1 / a := by
  unfold beta
  rw [Gamma_one, Gamma_add_one ha.ne']
  field_simp [(Gamma_pos_of_pos ha).ne', ha.ne']

/-- A power density is a gamma density with its exponential tilt removed. -/
theorem power_density (a x : ℝ) (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) 1) :
    betaPDF a 1 x = ofReal (a * Gamma a) * gammaPDF a 1 x * ofReal (exp x) := by
  have hΓ := Gamma_pos_of_pos ha
  have he : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  change ofReal (betaPDFReal a 1 x) =
    ofReal (a * Gamma a) * ofReal (gammaPDFReal a 1 x) * ofReal (exp x)
  rw [← ENNReal.ofReal_mul (mul_pos ha hΓ).le,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_pos ha hΓ).le
      (gammaPDFReal_nonneg ha zero_lt_one x))]
  congr 1
  simp only [betaPDFReal, ite_eq_left (show 0 < x ∧ x < 1 from hx), beta_one a ha, one_div_div,
    sub_self, rpow_zero, mul_one, gammaPDFReal, ite_eq_left hx.1.le,
    one_rpow, one_mul]
  symm
  calc
    _ = a * x ^ (a - 1) * (exp (-x) * exp x) := by field_simp [hΓ.ne']
    _ = _ := by rw [he]; ring

/-- On the unit interval the gamma tilt is a normalized power density. -/
theorem radial_density (t s : ℝ) (ht : 0 < t) (hs : s ∈ Ioo (0 : ℝ) 1) :
    gammaPDF t 1 s * ofReal (exp s) =
      ofReal (1 / (t * Gamma t)) * betaPDF t 1 s := by
  rw [power_density t s ht hs]
  have hC : ofReal (1 / (t * Gamma t)) * ofReal (t * Gamma t) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    field_simp [(Gamma_pos_of_pos ht).ne', ht.ne']
    norm_num
  calc
    _ = 1 * (gammaPDF t 1 s * ofReal (exp s)) := (one_mul _).symm
    _ = _ := by rw [← hC]; ring

/-- The strict source guard, with the returned proportion as its continuation. -/
def accepted (F : ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  if z.1 + z.2 < 1 then F (z.1 / (z.1 + z.2)) else 0

private theorem tilted_density (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : x ≠ 0) (hy : y ≠ 0) (F : ℝ → ℝ≥0∞) :
    betaPDF a 1 x * betaPDF b 1 y * accepted F (x, y) =
      ofReal (a * Gamma a * (b * Gamma b)) *
        (gammaPDF a 1 x * gammaPDF b 1 y *
          (if x + y < 1 then ofReal (exp (x + y)) * F (x / (x + y)) else 0)) := by
  by_cases hsum : x + y < 1
  · simp only [accepted, ite_eq_left hsum]
    rcases lt_or_gt_of_ne hx with hx | hx
    · rw [betaPDF_eq_zero_of_nonpos hx.le, gammaPDF_of_neg hx]
      simp
    · rcases lt_or_gt_of_ne hy with hy | hy
      · rw [betaPDF_eq_zero_of_nonpos hy.le, gammaPDF_of_neg hy]
        simp
      · rw [power_density a x ha ⟨hx, by linarith⟩,
          power_density b y hb ⟨hy, by linarith⟩, exp_add,
          ENNReal.ofReal_mul (exp_pos x).le,
          ENNReal.ofReal_mul (mul_pos ha (Gamma_pos_of_pos ha)).le]
        ring
  · simp [accepted, hsum]

private theorem transformed_density (a b s u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hs : s ≠ 0) (F : ℝ → ℝ≥0∞) :
    betaPDF a b u * gammaPDF (a + b) 1 s *
        (if s * u + s * (1 - u) < 1 then
          ofReal (exp (s * u + s * (1 - u))) *
            F (s * u / (s * u + s * (1 - u))) else 0) =
      ofReal (1 / ((a + b) * Gamma (a + b))) * betaPDF (a + b) 1 s *
        (betaPDF a b u * F u) := by
  have hsum : s * u + s * (1 - u) = s := by ring
  have hratio : s * u / s = u := by field_simp
  rw [hsum, hratio]
  rcases lt_or_gt_of_ne hs with hs | hs
  · rw [gammaPDF_of_neg hs, betaPDF_eq_zero_of_nonpos hs.le]
    simp
  · by_cases h1 : s < 1
    · rw [ite_eq_left h1]
      calc
        _ = (gammaPDF (a + b) 1 s * ofReal (exp s)) *
            (betaPDF a b u * F u) := by ring
        _ = _ := by rw [radial_density (a + b) s (add_pos ha hb) ⟨hs, h1⟩]
    · rw [ite_eq_right h1, betaPDF_eq_zero_of_one_le (not_lt.mp h1)]
      simp

/-- The accepted proportion has the beta density, scaled by its acceptance mass. -/
theorem density_expectation (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, betaPDF a 1 x * betaPDF b 1 y * accepted F (x, y)) =
      ofReal (a * b / (a + b) * beta a b) * ∫⁻ u, betaPDF a b u * F u := by
  let K := ofReal (a * Gamma a * (b * Gamma b))
  let C := ofReal (1 / ((a + b) * Gamma (a + b)))
  let G : ℝ × ℝ → ℝ≥0∞ := fun z =>
    if z.1 + z.2 < 1 then ofReal (exp (z.1 + z.2)) *
      F (z.1 / (z.1 + z.2)) else 0
  have hG : Measurable G := by
    apply Measurable.ite (isOpen_lt (by fun_prop) continuous_const).measurableSet
    · exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul (hF.comp (by fun_prop))
    · exact measurable_const
  have hK : K * C = ofReal (a * b / (a + b) * beta a b) := by
    dsimp [K, C]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold beta
    field_simp [(Gamma_pos_of_pos (add_pos ha hb)).ne', (add_pos ha hb).ne']
  calc
    _ = ∫⁻ x, ∫⁻ y, K * (gammaPDF a 1 x * gammaPDF b 1 y * G (x, y)) := by
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
      exact tilted_density a b x y ha hb hx hy F
    _ = K * ∫⁻ x, ∫⁻ y, gammaPDF a 1 x * gammaPDF b 1 y * G (x, y) := by
      simp_rw [lintegral_const_mul' K _ ENNReal.ofReal_ne_top]
    _ = K * ∫⁻ s, ∫⁻ u, betaPDF a b u * gammaPDF (a + b) 1 s *
        G (s * u, s * (1 - u)) := by
      rw [BetaExponentialProduct.gamma_pair_transform a b 1 ha hb zero_lt_one G hG]
    _ = K * ∫⁻ s, ∫⁻ u, C * betaPDF (a + b) 1 s * (betaPDF a b u * F u) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with s hs
      apply lintegral_congr
      intro u
      exact transformed_density a b s u ha hb hs F
    _ = K * (C * ∫⁻ u, betaPDF a b u * F u) := by
      congr 1
      calc
        _ = ∫⁻ s, (C * betaPDF (a + b) 1 s) *
            (∫⁻ u, betaPDF a b u * F u) := by
          apply lintegral_congr
          intro s
          exact lintegral_const_mul _ ((measurable_beta a b).mul hF)
        _ = (C * ∫⁻ u, betaPDF a b u * F u) * ∫⁻ s, betaPDF (a + b) 1 s := by
          rw [← lintegral_const_mul _ (measurable_beta (a + b) 1)]
          apply lintegral_congr
          intro s
          ring
        _ = _ := by
          rw [lintegral_betaPDF_eq_one (add_pos ha hb) zero_lt_one, mul_one]
    _ = _ := by rw [← mul_assoc, hK]

/-- Johnk's strictly positive probability of accepting a proposal. -/
def acceptance (a b : ℝ) : ℝ := a * b / (a + b) * beta a b

theorem acceptance_pos (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    0 < acceptance a b :=
  mul_pos (div_pos (mul_pos ha hb) (add_pos ha hb)) (beta_pos ha hb)

private theorem measurable_accepted (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (accepted F) :=
  Measurable.ite (isOpen_lt (by fun_prop) continuous_const).measurableSet
    (hF.comp (measurable_fst.div (measurable_fst.add measurable_snd))) measurable_const

/-- Exact rejection expectation, with arbitrary nonnegative extended-real credit. -/
theorem expectation (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ∫⁻ y, accepted F (x, y) ∂betaMeasure b 1 ∂betaMeasure a 1) =
      ofReal (acceptance a b) * ∫⁻ u, F u ∂betaMeasure a b := by
  let := isProbabilityMeasureBeta hb zero_lt_one
  have hacc := measurable_accepted F hF
  have hinner : Measurable (fun x => ∫⁻ y, accepted F (x, y) ∂betaMeasure b 1) :=
    hacc.lintegral_prod_right'
  have hfix (x : ℝ) : Measurable (fun y => accepted F (x, y)) :=
    hacc.comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ x, betaPDF a 1 x *
        (∫⁻ y, betaPDF b 1 y * accepted F (x, y)) := by
      rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_beta a 1) hinner]
      apply lintegral_congr
      intro x
      change betaPDF a 1 x * (∫⁻ y, accepted F (x, y) ∂betaMeasure b 1) = _
      rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _
        (measurable_beta b 1) (hfix x)]
      rfl
    _ = ∫⁻ x, ∫⁻ y, betaPDF a 1 x * betaPDF b 1 y * accepted F (x, y) := by
      apply lintegral_congr
      intro x
      rw [← lintegral_const_mul _ (show Measurable
        (fun y => betaPDF b 1 y * accepted F (x, y)) from
          (measurable_beta b 1).mul (hfix x))]
      apply lintegral_congr
      intro y
      ring
    _ = ofReal (acceptance a b) * ∫⁻ u, betaPDF a b u * F u :=
      density_expectation a b ha hb F hF
    _ = _ := by
      rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ (measurable_beta a b) hF]
      rfl

/-- The restricted proposal measure pushes forward to the beta law times its mass. -/
theorem accepted_map (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (((betaMeasure a 1).prod (betaMeasure b 1)).restrict
      {z : ℝ × ℝ | z.1 + z.2 < 1}).map
        (fun z : ℝ × ℝ => z.1 / (z.1 + z.2)) =
      ofReal (acceptance a b) • betaMeasure a b := by
  let := isProbabilityMeasureBeta ha zero_lt_one
  let := isProbabilityMeasureBeta hb zero_lt_one
  have hset : MeasurableSet {z : ℝ × ℝ | z.1 + z.2 < 1} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hratio : Measurable (fun z : ℝ × ℝ => z.1 / (z.1 + z.2)) := by fun_prop
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF hratio, ← lintegral_indicator hset, lintegral_smul_measure,
    smul_eq_mul]
  change (∫⁻ z, accepted F z ∂(betaMeasure a 1).prod (betaMeasure b 1)) = _
  rw [lintegral_prod _ (measurable_accepted F hF).aemeasurable]
  exact expectation a b ha hb F hF

/-- Normalizing the accepted proposals yields exactly the canonical beta measure. -/
theorem normalized_map (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (ofReal (acceptance a b))⁻¹ •
      ((((betaMeasure a 1).prod (betaMeasure b 1)).restrict
        {z : ℝ × ℝ | z.1 + z.2 < 1}).map
          (fun z : ℝ × ℝ => z.1 / (z.1 + z.2))) = betaMeasure a b := by
  rw [accepted_map a b ha hb, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (acceptance_pos a b ha hb)).ne'
      ENNReal.ofReal_ne_top, one_smul]

end
end SampLib.JohnkBeta
