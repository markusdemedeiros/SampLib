import SampLib.Bernoulli.Laws.LinearFactory
import SampLib.Continuous.Laws.IterateCoin

/-! # Integer stages of Huber's geometric-jump factory -/

open ProbLang

namespace SampLib.Linear2014

noncomputable section

structure Parameters (p : unitInterval) where
  a : ℤ
  b : ℤ
  e : ℤ
  f : ℤ
  numerator : ℤ
  denominator : ℤ
  b_pos : 0 < b
  b_lt_a : b < a
  e_pos : 0 < e
  e_lt_f : e < f
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator
  threshold : 2 * f * denominator ≤ e * numerator
  bound : Gambler.ratio p a b ≤ 1 - (e : ℝ) / f

namespace Parameters

variable {p : unitInterval} (σ : Parameters p)

theorem a_pos : 0 < σ.a := σ.b_pos.trans σ.b_lt_a

theorem f_pos : 0 < σ.f := σ.e_pos.trans σ.e_lt_f

def margin : ℝ := (σ.e : ℝ) / σ.f

theorem margin_pos : 0 < σ.margin :=
  div_pos (by exact_mod_cast σ.e_pos) (by exact_mod_cast σ.f_pos)

theorem margin_lt_one : σ.margin < 1 :=
  (div_lt_one (by exact_mod_cast σ.f_pos)).mpr (by exact_mod_cast σ.e_lt_f)

def bias : unitInterval :=
  ⟨Gambler.ratio p σ.a σ.b, Gambler.ratio_nonneg p σ.a σ.b σ.a_pos σ.b_pos,
    σ.bound.trans (sub_le_self _ σ.margin_pos.le)⟩

@[simp] theorem bias_coe : (σ.bias : ℝ) = Gambler.ratio p σ.a σ.b := rfl

theorem bias_lt_one : (σ.bias : ℝ) < 1 := lt_of_le_of_lt σ.bound (by
  exact sub_lt_self _ σ.margin_pos)

def factorNum : ℤ := 2 * σ.f + σ.e

def factorDen : ℤ := 2 * σ.f

theorem factorDen_pos : 0 < σ.factorDen := mul_pos (by norm_num) σ.f_pos

theorem factor_lt : σ.factorDen < σ.factorNum := by
  dsimp [factorDen, factorNum]
  exact lt_add_of_pos_right _ σ.e_pos

theorem factorNum_pos : 0 < σ.factorNum := σ.factorDen_pos.trans σ.factor_lt

theorem factor_ratio : (σ.factorNum : ℝ) / σ.factorDen = 1 + σ.margin / 2 := by
  have hf : (σ.f : ℝ) ≠ 0 := by exact_mod_cast σ.f_pos.ne'
  simp only [factorNum, factorDen, margin, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  field_simp

private theorem next_ratio : Gambler.ratio p (σ.a * σ.factorNum) (σ.b * σ.factorDen) =
    (σ.bias : ℝ) * (1 + σ.margin / 2) := by
  rw [← σ.factor_ratio]
  simp only [Gambler.ratio, bias_coe, Int.cast_mul]
  ring

def next : Parameters p where
  a := σ.a * σ.factorNum
  b := σ.b * σ.factorDen
  e := σ.e
  f := 2 * σ.f
  numerator := 2 * σ.numerator
  denominator := σ.denominator
  b_pos := mul_pos σ.b_pos σ.factorDen_pos
  b_lt_a := mul_lt_mul_of_pos_of_nonneg' σ.b_lt_a σ.factor_lt.le
    σ.factorDen_pos σ.a_pos.le
  e_pos := σ.e_pos
  e_lt_f := by have := σ.e_lt_f; have := σ.f_pos; omega
  numerator_pos := mul_pos (by norm_num) σ.numerator_pos
  denominator_pos := σ.denominator_pos
  threshold := by nlinarith [σ.threshold]
  bound := by
    rw [next_ratio]
    have hβ : 0 < 1 + σ.margin / 2 := by have := σ.margin_pos; linarith
    have hbound : (σ.bias : ℝ) ≤ 1 - σ.margin := σ.bound
    have h := mul_le_mul_of_nonneg_right hbound hβ.le
    have he := σ.margin_pos
    have hsq := sq_nonneg σ.margin
    simp only [Int.cast_mul, Int.cast_ofNat]
    change (σ.bias : ℝ) * (1 + σ.margin / 2) ≤ 1 - (σ.e : ℝ) / (2 * σ.f)
    have hhalf : (σ.e : ℝ) / (2 * σ.f) = σ.margin / 2 := by dsimp [margin]; ring
    rw [hhalf]
    nlinarith

@[simp] theorem next_margin : σ.next.margin = σ.margin / 2 := by
  simp only [next, margin, Int.cast_mul, Int.cast_ofNat]
  ring

theorem next_bias : (σ.next.bias : ℝ) = (σ.bias : ℝ) * (1 + σ.margin / 2) :=
  σ.next_ratio

def jumpBias : unitInterval :=
  RationalCoin.bias (σ.a - σ.b) σ.a (sub_pos.mpr σ.b_lt_a).le σ.a_pos (by
    have := σ.b_pos
    omega)

theorem jumpBias_pos : 0 < (σ.jumpBias : ℝ) := by
  exact div_pos (by exact_mod_cast sub_pos.mpr σ.b_lt_a) (by exact_mod_cast σ.a_pos)

theorem jumpBias_lt_one : (σ.jumpBias : ℝ) < 1 := by
  change ((σ.a - σ.b : ℤ) : ℝ) / σ.a < 1
  apply (div_lt_one (by exact_mod_cast σ.a_pos)).mpr
  exact_mod_cast sub_lt_self σ.a σ.b_pos

theorem jump_relation : (1 - (σ.jumpBias : ℝ)) * (σ.bias : ℝ) = p := by
  have ha : (σ.a : ℝ) ≠ 0 := by exact_mod_cast σ.a_pos.ne'
  have hb : (σ.b : ℝ) ≠ 0 := by exact_mod_cast σ.b_pos.ne'
  simp only [jumpBias, RationalCoin.bias, bias_coe, Gambler.ratio, Int.cast_sub]
  field_simp
  ring

include σ in
theorem input_lt_one : (p : ℝ) < 1 := by
  rw [← σ.jump_relation]
  have hq := σ.jumpBias_pos
  have hq' := σ.jumpBias_lt_one
  have ht := σ.bias_lt_one
  have ht' := σ.bias.2.1
  nlinarith

theorem crossing (n : ℕ) (h : σ.numerator ≤ (n : ℤ) * σ.denominator) :
    2 ≤ (n : ℝ) * σ.margin := by
  have hn := mul_le_mul_of_nonneg_left h σ.e_pos.le
  have ht := σ.threshold.trans hn
  have hd : 0 < σ.denominator := σ.denominator_pos
  have hi : 2 * σ.f ≤ σ.e * (n : ℤ) := by nlinarith
  have hr : 2 * (σ.f : ℝ) ≤ (σ.e : ℝ) * n := by exact_mod_cast hi
  rw [margin, ← mul_div_assoc, le_div_iff₀ (by exact_mod_cast σ.f_pos)]
  nlinarith

def selectorBase : unitInterval :=
  RationalCoin.bias σ.factorDen σ.factorNum σ.factorDen_pos.le σ.factorNum_pos σ.factor_lt.le

def selector (n : ℕ) : unitInterval := IterateCoin.bias σ.selectorBase n

theorem selector_coe (n : ℕ) : (σ.selector n : ℝ) = 1 / (1 + σ.margin / 2) ^ n := by
  have hf : (σ.f : ℝ) ≠ 0 := by exact_mod_cast σ.f_pos.ne'
  have hn : 0 < 2 * (σ.f : ℝ) + σ.e := by exact_mod_cast σ.factorNum_pos
  simp only [selector, IterateCoin.bias, selectorBase, RationalCoin.bias,
    factorNum, factorDen, margin, Int.cast_mul, Int.cast_add, Int.cast_ofNat, ← one_div_pow]
  congr 1
  field_simp

/-- The source's initial threshold is `23/(5ε)`; its optional clamp only enlarges slack. -/
def initial (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) : Parameters p :=
  if hc : 1000 * e ≤ 644 * f then
    { a := a, b := b, e := e, f := f, numerator := 23 * f, denominator := 5 * e
      b_pos := h.2.1
      b_lt_a := hba
      e_pos := (h.2.2 hba).1
      e_lt_f := (h.2.2 hba).2.1
      numerator_pos := mul_pos (by norm_num) ((h.2.2 hba).1.trans (h.2.2 hba).2.1)
      denominator_pos := mul_pos (by norm_num) (h.2.2 hba).1
      threshold := by
        have he := (h.2.2 hba).1
        have hf := he.trans (h.2.2 hba).2.1
        nlinarith [mul_pos he hf]
      bound := (h.2.2 hba).2.2 }
  else
    { a := a, b := b, e := 644, f := 1000, numerator := 23000, denominator := 3220
      b_pos := h.2.1
      b_lt_a := hba
      e_pos := by norm_num
      e_lt_f := by norm_num
      numerator_pos := by norm_num
      denominator_pos := by norm_num
      threshold := by norm_num
      bound := by
        have hf : 0 < (f : ℝ) := by
          exact_mod_cast (h.2.2 hba).1.trans (h.2.2 hba).2.1
        have hc' : 644 * (f : ℝ) < 1000 * e := by exact_mod_cast lt_of_not_ge hc
        have hm : (644 : ℝ) / 1000 ≤ (e : ℝ) / f := by
          apply (le_div_iff₀ hf).mpr
          nlinarith
        exact (h.2.2 hba).2.2.trans (sub_le_sub_left hm 1) }

theorem initial_bias (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) :
    (initial p a b e f h hba).bias = LinearFactory.bias p a b e f h := by
  unfold initial
  split <;> apply Subtype.ext <;> rfl

end Parameters

end

end SampLib.Linear2014
