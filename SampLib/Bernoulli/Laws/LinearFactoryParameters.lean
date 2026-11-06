import SampLib.Bernoulli.Laws.Gambler

/-! # Parameters of the adaptive linear factory

A parameter record holds the integer coefficient `a/b` and the margin `e/f`. When the
coefficient expands, the next stage rescales the margin so that the expected number of
recursive calls stays below one.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal BigOperators

namespace SampLib.LinearFactory

noncomputable section

/-- Margin arguments are inspected only when the rational coefficient expands. -/
def Admissible (p : unitInterval) (a b e f : ℤ) : Prop :=
  0 ≤ a ∧ 0 < b ∧ (b < a → 0 < e ∧ e < f ∧ Gambler.ratio p a b ≤ 1 - (e : ℝ) / f)

/-- The complete integer parameter domain, including contracting and zero coefficients. -/
structure Parameters (p : unitInterval) where
  a : ℤ
  b : ℤ
  e : ℤ
  f : ℤ
  admissible : Admissible p a b e f

namespace Parameters

variable {p : unitInterval}

theorem nonneg (σ : Parameters p) : 0 ≤ Gambler.ratio p σ.a σ.b :=
  div_nonneg (mul_nonneg (by exact_mod_cast σ.admissible.1) p.2.1)
    (by exact_mod_cast σ.admissible.2.1.le)

theorem le_one (σ : Parameters p) : Gambler.ratio p σ.a σ.b ≤ 1 := by
  by_cases h : σ.a ≤ σ.b
  · apply (div_le_one (show 0 < (σ.b : ℝ) by exact_mod_cast σ.admissible.2.1)).mpr
    calc
      (σ.a : ℝ) * p ≤ (σ.a : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left p.2.2 (by exact_mod_cast σ.admissible.1)
      _ ≤ σ.b := by simpa using (show (σ.a : ℝ) ≤ σ.b by exact_mod_cast h)
  · obtain ⟨he, hef, hm⟩ := σ.admissible.2.2 (lt_of_not_ge h)
    exact hm.trans (sub_le_self _ (div_nonneg (by exact_mod_cast he.le)
      (by exact_mod_cast (he.trans hef).le)))

/-- The requested linear bias, independent of the algorithm's adaptive steps. -/
def bias (σ : Parameters p) : unitInterval :=
  ⟨Gambler.ratio p σ.a σ.b, σ.nonneg, σ.le_one⟩

@[simp] theorem bias_coe (σ : Parameters p) :
    (σ.bias : ℝ) = Gambler.ratio p σ.a σ.b := rfl

end Parameters

/-- The source's integer implementation of `ceil (9f/(2e)) + 1`. -/
def scale (e f : ℤ) : ℤ := (9 * f + 2 * e - 1) / (2 * e) + 1

theorem scale_pred (e f : ℤ) : (9 * f + 2 * e - 1) / (2 * e) = scale e f - 1 := by
  simp [scale]

theorem scale_bounds (e f : ℤ) (he : 0 < e) (hef : e < f) :
    2 ≤ scale e f ∧ 7 * f ≤ 2 * (scale e f * e - f) := by
  have hf := he.trans hef
  have hd : 0 < 2 * e := by omega
  have hr := Int.emod_lt_of_pos (9 * f + 2 * e - 1) hd
  have hdiv := Int.ediv_mul_add_emod (9 * f + 2 * e - 1) (2 * e)
  have hround : 9 * f ≤ ((9 * f + 2 * e - 1) / (2 * e)) * (2 * e) := by
    nlinarith
  constructor
  · by_contra! h
    have hq : (9 * f + 2 * e - 1) / (2 * e) ≤ 0 := by dsimp [scale] at h; omega
    have hprod := mul_nonpos_of_nonpos_of_nonneg hq hd.le
    omega
  · dsimp [scale]
    nlinarith

namespace Parameters

variable {p : unitInterval}

theorem scale_pos (σ : Parameters p) (h : σ.b < σ.a) : 0 < scale σ.e σ.f := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  exact lt_of_lt_of_le (by norm_num) (scale_bounds σ.e σ.f he hef).1

theorem next_margin (σ : Parameters p) (h : σ.b < σ.a) :
    0 < scale σ.e σ.f * σ.e - σ.f ∧
      scale σ.e σ.f * σ.e - σ.f < (scale σ.e σ.f - 1) * σ.f := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  obtain ⟨hm, hbound⟩ := scale_bounds σ.e σ.f he hef
  constructor
  · nlinarith [he.trans hef]
  · have hp := mul_pos (σ.scale_pos h) (sub_pos.mpr hef)
    nlinarith

theorem next_ratio (σ : Parameters p) (h : σ.b < σ.a) :
    Gambler.ratio p (σ.a * scale σ.e σ.f) (σ.b * (scale σ.e σ.f - 1)) =
      (σ.bias : ℝ) * (scale σ.e σ.f : ℝ) / ((scale σ.e σ.f : ℝ) - 1) := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  have hm : 2 ≤ scale σ.e σ.f := (scale_bounds σ.e σ.f he hef).1
  have hb : (σ.b : ℝ) ≠ 0 := by exact_mod_cast σ.admissible.2.1.ne'
  have hm1 : (scale σ.e σ.f : ℝ) - 1 ≠ 0 := by exact_mod_cast (show scale σ.e σ.f - 1 ≠ 0 by omega)
  simp only [Gambler.ratio, bias_coe, Int.cast_mul, Int.cast_sub, Int.cast_one]
  field_simp

theorem next_bound (σ : Parameters p) (h : σ.b < σ.a) :
    Gambler.ratio p (σ.a * scale σ.e σ.f) (σ.b * (scale σ.e σ.f - 1)) ≤
      1 - ((scale σ.e σ.f * σ.e - σ.f : ℤ) : ℝ) /
        (((scale σ.e σ.f - 1) * σ.f : ℤ) : ℝ) := by
  obtain ⟨he, hef, hr⟩ := σ.admissible.2.2 h
  have hm := (scale_bounds σ.e σ.f he hef).1
  have hf : 0 < (σ.f : ℝ) := by exact_mod_cast he.trans hef
  have hm1 : 0 < (scale σ.e σ.f : ℝ) - 1 := by exact_mod_cast (show 0 < scale σ.e σ.f - 1 by omega)
  rw [next_ratio σ h]
  calc
    _ ≤ (1 - (σ.e : ℝ) / σ.f) * (scale σ.e σ.f : ℝ) /
        ((scale σ.e σ.f : ℝ) - 1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr (by exact_mod_cast (σ.scale_pos h).le)) hm1.le
    _ = _ := by
      push_cast
      field_simp
      ring

/-- The recursive call inherits a valid, generally smaller, positive margin. -/
def next (σ : Parameters p) (h : σ.b < σ.a) : Parameters p where
  a := σ.a * scale σ.e σ.f
  b := σ.b * (scale σ.e σ.f - 1)
  e := scale σ.e σ.f * σ.e - σ.f
  f := (scale σ.e σ.f - 1) * σ.f
  admissible := by
    obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
    have hm := (scale_bounds σ.e σ.f he hef).1
    refine ⟨mul_nonneg σ.admissible.1 (σ.scale_pos h).le,
      mul_pos σ.admissible.2.1 (by omega), fun _ => ?_⟩
    exact ⟨(σ.next_margin h).1, (σ.next_margin h).2, σ.next_bound h⟩

@[simp] theorem next_a (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.next h).a = σ.a * scale σ.e σ.f := rfl

@[simp] theorem next_b (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.next h).b = σ.b * (scale σ.e σ.f - 1) := rfl

@[simp] theorem next_e (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.next h).e = scale σ.e σ.f * σ.e - σ.f := rfl

@[simp] theorem next_f (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.next h).f = (scale σ.e σ.f - 1) * σ.f := rfl

theorem next_a_pos (σ : Parameters p) (h : σ.b < σ.a) : 0 < (σ.next h).a :=
  mul_pos (σ.admissible.2.1.trans h) (σ.scale_pos h)

theorem next_bias_lt_one (σ : Parameters p) (h : σ.b < σ.a) : ((σ.next h).bias : ℝ) < 1 := by
  have he : 0 < ((σ.next h).e : ℝ) := by exact_mod_cast (σ.next_margin h).1
  have hf : 0 < ((σ.next h).f : ℝ) := by
    exact_mod_cast (σ.next_margin h).1.trans (σ.next_margin h).2
  exact lt_of_le_of_lt (σ.next_bound h) (sub_lt_self _ (div_pos he hf))

/-- The supplied margin bounds the expected number of immediate recursive factory calls by `2/7`. -/
theorem offspring_bound (σ : Parameters p) (h : σ.b < σ.a) :
    1 / (scale σ.e σ.f : ℝ) * (1 / (1 - ((σ.next h).bias : ℝ))) ≤ 2 / 7 := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  obtain ⟨hm, hs⟩ := scale_bounds σ.e σ.f he hef
  have hf : 0 < (σ.f : ℝ) := by exact_mod_cast he.trans hef
  have hm1 : 0 < (scale σ.e σ.f : ℝ) - 1 := by
    exact_mod_cast (show 0 < scale σ.e σ.f - 1 by omega)
  have he' : 0 < ((σ.next h).e : ℝ) := by exact_mod_cast (σ.next_margin h).1
  have hε : ((σ.next h).e : ℝ) / (σ.next h).f ≤ 1 - ((σ.next h).bias : ℝ) := by
    have hn := σ.next_bound h
    change ((σ.next h).bias : ℝ) ≤ 1 - ((σ.next h).e : ℝ) / (σ.next h).f at hn
    linarith
  have hscale : 1 ≤ (scale σ.e σ.f : ℝ) / ((scale σ.e σ.f : ℝ) - 1) :=
    (le_div_iff₀ hm1).mpr (by linarith)
  have hlower : (7 / 2 : ℝ) ≤ (scale σ.e σ.f : ℝ) * (1 - ((σ.next h).bias : ℝ)) := by
    calc
      _ ≤ ((σ.next h).e : ℝ) / σ.f := by
        apply (le_div_iff₀ hf).mpr
        have hr : 7 * (σ.f : ℝ) ≤ 2 * ((σ.next h).e : ℝ) := by exact_mod_cast hs
        linarith
      _ ≤ (((σ.next h).e : ℝ) / σ.f) *
          ((scale σ.e σ.f : ℝ) / ((scale σ.e σ.f : ℝ) - 1)) := by
        exact le_mul_of_one_le_right (div_nonneg he'.le hf.le) hscale
      _ = (scale σ.e σ.f : ℝ) * (((σ.next h).e : ℝ) / (σ.next h).f) := by
        simp only [next, Int.cast_mul, Int.cast_sub, Int.cast_one]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hε (by exact_mod_cast (σ.scale_pos h).le)
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7 / 2) hlower
  simpa only [one_div_mul_one_div, one_div_div, div_one] using hinv

end Parameters

end

end SampLib.LinearFactory
