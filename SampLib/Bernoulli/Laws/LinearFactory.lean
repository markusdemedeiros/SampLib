import SampLib.Bernoulli.HighPowerLogistic

/-! # The adaptive linear factory

The finite inner loop has a geometric-sum success law. Its expected number of
recursive factory calls is bounded by the supplied margin, making the adaptive
recursion subcritical without imposing a well-founded order on the margins.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal BigOperators

namespace SampLib.LinearFactory

noncomputable section

set_option maxHeartbeats 600000

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

private abbrev S (t : unitInterval) (n : ℕ) : ℝ := FiniteGeometricWalk.total (t : ℝ) n

/-- Success bias of the high-power subroutine. -/
def powerBias (t : unitInterval) (n : ℕ) : unitInterval :=
  FiniteGeometricWalk.bias (t : ℝ) t.2.1 (n + 1) (Nat.succ_pos _) n

@[simp] theorem powerBias_coe (t : unitInterval) (n : ℕ) :
    (powerBias t n : ℝ) = (t : ℝ) ^ n / S t (n + 1) := by
  simp [powerBias, FiniteGeometricWalk.bias, FiniteGeometricWalk.tail]

@[simp] theorem powerBias_zero (t : unitInterval) : powerBias t 0 = 1 := by
  exact FiniteGeometricWalk.bias_zero _ _ _ _

private theorem inner_numerator_le (t : unitInterval) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * (t : ℝ) ^ (n + 1) ≤ S t (n + 1) := by
  calc
    _ = ∑ j ∈ Finset.range (n + 1), (t : ℝ) ^ (n + 1) := by simp
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
      pow_le_pow_of_le_one t.2.1 t.2.2 (Finset.mem_range.mp hj).le

/-- Inner-loop success probability at height `n + 2`. -/
def innerBias (t : unitInterval) (n : ℕ) : unitInterval :=
  ⟨((n + 1 : ℕ) : ℝ) * (t : ℝ) ^ (n + 1) / S t (n + 1),
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg t.2.1 _))
      (FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos _)).le,
    (div_le_one (FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos _))).mpr
      (inner_numerator_le t n)⟩

theorem innerBias_zero (t : unitInterval) : innerBias t 0 = t := by
  apply Subtype.ext
  simp [innerBias, FiniteGeometricWalk.total]

theorem innerBias_succ (t : unitInterval) (n : ℕ) :
    (innerBias t (n + 1) : ℝ) = (t : ℝ) *
      ((powerBias t (n + 1) : ℝ) + (1 - (powerBias t (n + 1) : ℝ)) * innerBias t n) := by
  have hS : S t (n + 2) = S t (n + 1) + (t : ℝ) ^ (n + 1) :=
    Finset.sum_range_succ _ _
  simp only [innerBias, powerBias_coe, Nat.cast_add, Nat.cast_one]
  field_simp [(FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos n)).ne',
    (FiniteGeometricWalk.total_pos _ t.2.1 _ (Nat.succ_pos (n + 1))).ne']
  simp only [Nat.add_assoc]
  rw [hS, pow_succ]
  ring

/-- Expected recursive calls made by the finite inner loop at height `n + 2`. -/
def calls (t : unitInterval) : ℕ → ℝ
  | 0 => 1
  | n + 1 => 1 + (t : ℝ) * (1 - (powerBias t (n + 1) : ℝ)) * calls t n

theorem calls_nonneg (t : unitInterval) (n : ℕ) : 0 ≤ calls t n := by
  induction n with
  | zero => norm_num [calls]
  | succ n ih =>
    exact add_nonneg zero_le_one
      (mul_nonneg (mul_nonneg t.2.1 (sub_nonneg.mpr (powerBias t (n + 1)).2.2)) ih)

/-- Each additional call requires another success of the transformed input coin. -/
theorem calls_le (t : unitInterval) (ht : (t : ℝ) < 1) (n : ℕ) :
    calls t n ≤ 1 / (1 - (t : ℝ)) := by
  have hd : 0 < 1 - (t : ℝ) := sub_pos.mpr ht
  induction n with
  | zero =>
    simpa only [calls] using (one_le_div hd).mpr (by linarith [t.2.1])
  | succ n ih =>
    have hw : 0 ≤ (t : ℝ) * (1 - (powerBias t (n + 1) : ℝ)) :=
      mul_nonneg t.2.1 (sub_nonneg.mpr (powerBias t (n + 1)).2.2)
    calc
      _ ≤ 1 + ((t : ℝ) * (1 - (powerBias t (n + 1) : ℝ))) * (1 / (1 - (t : ℝ))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ih hw)
      _ ≤ 1 + (t : ℝ) * (1 / (1 - (t : ℝ))) := by
        gcongr
        exact mul_le_of_le_one_right t.2.1 (sub_le_self _ (powerBias t (n + 1)).2.1)
      _ = _ := by field_simp; ring

private theorem coin_credit_zero (F : Bool → ℝ≥0∞) : RealCoin.credit 0 F = F false := by
  simp [RealCoin.credit, RealCoin.pmf]

private theorem coin_credit_one (F : Bool → ℝ≥0∞) : RealCoin.credit 1 F = F true := by
  simp [RealCoin.credit, RealCoin.pmf]

private theorem mixture_credit (p q r : unitInterval) (F : Bool → ℝ≥0∞) :
    RealCoin.credit r (fun b => if b then RealCoin.credit p F else RealCoin.credit q F) =
      RealCoin.credit (CoinConditional.bias p q r) F := by
  simpa only [RealCoin.lintegral_law, CoinConditional.firstCredit, CoinConditional.law] using
    CoinConditional.expectation_preservation p q r F

def retryCredit (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if n = 0 then F false
  else RealCoin.credit (innerBias t (n - 1)) F + ofReal (calls t (n - 1)) * δ

def powerCredit (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ)
    (b : Bool) : ℝ≥0∞ :=
  if b then F true else retryCredit t F δ n

def factoryCredit (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ)
    (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, powerCredit t F δ n z ∂RealCoin.law (powerBias t n) else F false

/-- One finite-loop step preserves its geometric success law and pays exactly one factory call. -/
theorem inner_expectation (t : unitInterval) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (n : ℕ) :
    RealCoin.credit t (factoryCredit t F δ n) + δ =
      RealCoin.credit (innerBias t n) F + ofReal (calls t n) * δ := by
  cases n with
  | zero =>
    simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, factoryCredit, powerCredit,
      retryCredit, powerBias_zero, innerBias_zero, calls]
  | succ n =>
    have hbias : CoinConditional.bias
        (CoinConditional.bias 1 (innerBias t n) (powerBias t (n + 1))) 0 t =
        innerBias t (n + 1) := by
      apply Subtype.ext
      change (1 - (t : ℝ)) * 0 + (t : ℝ) *
        ((1 - (powerBias t (n + 1) : ℝ)) * innerBias t n +
          (powerBias t (n + 1) : ℝ) * 1) = _
      rw [innerBias_succ]
      ring
    have hinner := mixture_credit 1 (innerBias t n) (powerBias t (n + 1)) F
    have houter := mixture_credit
      (CoinConditional.bias 1 (innerBias t n) (powerBias t (n + 1))) 0 t F
    simp only [coin_credit_one] at hinner
    simp only [coin_credit_zero] at houter
    rw [← hinner, hbias] at houter
    have hq := sub_nonneg.mpr (powerBias t (n + 1)).2.2
    have hcalls : ofReal (t : ℝ) * ofReal (1 - (powerBias t (n + 1) : ℝ)) *
        ofReal (calls t n) + 1 = ofReal (calls t (n + 1)) := by
      rw [calls, ENNReal.ofReal_add zero_le_one
          (mul_nonneg (mul_nonneg t.2.1 hq) (calls_nonneg t n)),
        ENNReal.ofReal_mul (mul_nonneg t.2.1 hq), ENNReal.ofReal_mul t.2.1,
        ENNReal.ofReal_one]
      ring
    calc
      _ = RealCoin.credit t (fun b => if b then
          RealCoin.credit (powerBias t (n + 1))
            (fun z => if z then F true else RealCoin.credit (innerBias t n) F)
          else F false) +
          (ofReal (t : ℝ) * ofReal (1 - (powerBias t (n + 1) : ℝ)) *
            ofReal (calls t n) + 1) * δ := by
        simp only [factoryCredit, powerCredit, retryCredit, Nat.add_one_ne_zero,
          ite_false, Nat.add_sub_cancel, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
          ite_true, Bool.false_eq_true]
        ring
      _ = _ := by rw [houter, hcalls]

namespace Parameters

variable {p : unitInterval}

/-- Integer-to-natural transport for the finite walk's height. -/
def height (σ : Parameters p) : ℕ := (scale σ.e σ.f).toNat

theorem height_cast (σ : Parameters p) (h : σ.b < σ.a) :
    ((σ.height : ℕ) : ℤ) = scale σ.e σ.f :=
  Int.toNat_of_nonneg (σ.scale_pos h).le

theorem height_two (σ : Parameters p) (h : σ.b < σ.a) : 2 ≤ σ.height := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  have hm := (scale_bounds σ.e σ.f he hef).1
  exact_mod_cast (show (2 : ℤ) ≤ (σ.height : ℤ) by rw [σ.height_cast h]; exact hm)

theorem height_real (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.height : ℝ) = (scale σ.e σ.f : ℝ) := by exact_mod_cast σ.height_cast h

theorem selector_bounds (σ : Parameters p) (h : σ.b < σ.a) :
    0 ≤ scale σ.e σ.f - 1 ∧ 0 < scale σ.e σ.f ∧ scale σ.e σ.f - 1 ≤ scale σ.e σ.f := by
  have hm := σ.scale_pos h
  omega

/-- Rational selector used after the outer walk succeeds. -/
def selector (σ : Parameters p) (h : σ.b < σ.a) : unitInterval :=
  RationalCoin.bias (scale σ.e σ.f - 1) (scale σ.e σ.f)
    (σ.selector_bounds h).1 (σ.selector_bounds h).2.1 (σ.selector_bounds h).2.2

@[simp] theorem selector_coe (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.selector h : ℝ) = ((σ.height : ℝ) - 1) / σ.height := by
  simp only [selector, RationalCoin.bias, Int.cast_sub, Int.cast_one, σ.height_real h]

theorem selector_complement (σ : Parameters p) (h : σ.b < σ.a) :
    1 - (σ.selector h : ℝ) = 1 / (scale σ.e σ.f : ℝ) := by
  have hm : (scale σ.e σ.f : ℝ) ≠ 0 := by exact_mod_cast (σ.scale_pos h).ne'
  rw [selector_coe, σ.height_real h]
  field_simp
  ring

/-- The normalized lower-exit law of the outer walk. -/
def walkBias (σ : Parameters p) (h : σ.b < σ.a) : unitInterval :=
  Gambler.bias p (σ.next h).a (σ.next h).b (σ.next_a_pos h)
    (σ.next h).admissible.2.1 σ.height

private theorem tail_one (t : unitInterval) (N : ℕ) :
    FiniteGeometricWalk.tail (t : ℝ) N 1 = (t : ℝ) * S t (N - 1) := by
  simp [FiniteGeometricWalk.tail, Finset.sum_Ico_eq_sum_range,
    pow_add, S, FiniteGeometricWalk.total, Finset.mul_sum]

theorem walkBias_coe (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.walkBias h : ℝ) = ((σ.next h).bias : ℝ) *
      S (σ.next h).bias (σ.height - 1) / S (σ.next h).bias σ.height := by
  have hm : 1 ≤ σ.height := le_trans (by norm_num) (σ.height_two h)
  change FiniteGeometricWalk.tail ((σ.next h).bias : ℝ) (max σ.height 1) 1 /
    S (σ.next h).bias (max σ.height 1) = _
  rw [max_eq_left hm, tail_one]

theorem bias_from_next (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.bias : ℝ) = ((σ.next h).bias : ℝ) * ((σ.height : ℝ) - 1) / σ.height := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  have hm := (scale_bounds σ.e σ.f he hef).1
  have hn := σ.next_ratio h
  change ((σ.next h).bias : ℝ) =
    (σ.bias : ℝ) * (scale σ.e σ.f : ℝ) / ((scale σ.e σ.f : ℝ) - 1) at hn
  have hm0 : (scale σ.e σ.f : ℝ) ≠ 0 := by exact_mod_cast (σ.scale_pos h).ne'
  have hm1 : (scale σ.e σ.f : ℝ) - 1 ≠ 0 := by
    exact_mod_cast (show scale σ.e σ.f - 1 ≠ 0 by omega)
  rw [σ.height_real h]
  field_simp at hn ⊢
  linarith

/-- The walk, rational gate, and inner loop compose to the requested linear bias. -/
theorem outer_bias (σ : Parameters p) (h : σ.b < σ.a) :
    CoinConditional.bias
      (CoinConditional.bias 1 (innerBias (σ.next h).bias (σ.height - 2)) (σ.selector h))
      0 (σ.walkBias h) = σ.bias := by
  let t := (σ.next h).bias
  have hM := σ.height_two h
  have hp : 0 < σ.height - 1 := by omega
  have hSM := FiniteGeometricWalk.total_pos (t : ℝ) t.2.1 σ.height (by omega)
  have hSp := FiniteGeometricWalk.total_pos (t : ℝ) t.2.1 (σ.height - 1) hp
  have hS : S t σ.height = S t (σ.height - 1) + (t : ℝ) ^ (σ.height - 1) := by
    simpa only [S, FiniteGeometricWalk.total,
      Nat.sub_add_cancel (show 1 ≤ σ.height by omega)] using
      Finset.sum_range_succ (fun j => (t : ℝ) ^ j) (σ.height - 1)
  have hm0 : (σ.height : ℝ) ≠ 0 := by exact_mod_cast (show σ.height ≠ 0 by omega)
  apply Subtype.ext
  change (1 - (σ.walkBias h : ℝ)) * 0 + (σ.walkBias h : ℝ) *
    ((1 - (σ.selector h : ℝ)) * (innerBias t (σ.height - 2) : ℝ) +
      (σ.selector h : ℝ) * 1) = (σ.bias : ℝ)
  rw [σ.walkBias_coe h, σ.selector_coe h, σ.bias_from_next h]
  change _ = (t : ℝ) * ((σ.height : ℝ) - 1) / σ.height
  simp only [innerBias, show σ.height - 2 + 1 = σ.height - 1 by omega]
  have hcast : ((σ.height - 1 : ℕ) : ℝ) = (σ.height : ℝ) - 1 := by
    have hc : ((σ.height - 1 : ℕ) : ℝ) = (σ.height : ℝ) - ((1 : ℕ) : ℝ) :=
      Nat.cast_sub (show 1 ≤ σ.height by omega)
    simpa only [Nat.cast_one] using hc
  rw [hcast]
  dsimp only [t] at hS hSM hSp ⊢
  field_simp [hSM.ne', hSp.ne', hm0]
  rw [hS]
  ring

theorem expected_calls_bound (σ : Parameters p) (h : σ.b < σ.a) :
    (σ.walkBias h : ℝ) * (1 - (σ.selector h : ℝ)) *
      calls (σ.next h).bias (σ.height - 2) ≤ 2 / 7 := by
  have hm : 0 < (scale σ.e σ.f : ℝ) := by exact_mod_cast σ.scale_pos h
  have hc := calls_nonneg (σ.next h).bias (σ.height - 2)
  rw [σ.selector_complement h]
  calc
    _ ≤ 1 * (1 / (scale σ.e σ.f : ℝ)) * calls (σ.next h).bias (σ.height - 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (σ.walkBias h).2.2 (one_div_nonneg.mpr hm.le)) hc
    _ = (1 / (scale σ.e σ.f : ℝ)) * calls (σ.next h).bias (σ.height - 2) := by ring
    _ ≤ (1 / (scale σ.e σ.f : ℝ)) * (1 / (1 - ((σ.next h).bias : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (calls_le _ (σ.next_bias_lt_one h) _) (one_div_nonneg.mpr hm.le)
    _ ≤ _ := σ.offspring_bound h

end Parameters

/-- The normalized requested bias `(a/b)*p`, with margins used only to establish its domain. -/
def bias (p : unitInterval) (a b e f : ℤ) (h : Admissible p a b e f) : unitInterval :=
  (Parameters.mk a b e f h).bias

@[simp] theorem bias_coe (p : unitInterval) (a b e f : ℤ) (h : Admissible p a b e f) :
    (bias p a b e f h : ℝ) = (a : ℝ) * p / b := rfl

/-- Conditional credit in the contracting branch. -/
def contractingCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, F z ∂RealCoin.law p else F false

theorem contracting_expectation {p : unitInterval} (σ : Parameters p) (hab : σ.a ≤ σ.b)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ b, contractingCredit p F b ∂RealCoin.law
      (RationalCoin.bias σ.a σ.b σ.admissible.1 σ.admissible.2.1 hab) =
      RealCoin.credit σ.bias F := by
  let r := RationalCoin.bias σ.a σ.b σ.admissible.1 σ.admissible.2.1 hab
  have hbias : CoinConditional.bias p 0 r = σ.bias := by
    apply Subtype.ext
    change (1 - (r : ℝ)) * 0 + (r : ℝ) * p = (σ.a : ℝ) * p / σ.b
    dsimp [r, RationalCoin.bias]
    ring
  simpa only [contractingCredit, CoinConditional.firstCredit, CoinConditional.law,
    RealCoin.lintegral_law, coin_credit_zero, hbias] using
    CoinConditional.expectation_preservation p 0 r F

def selectorCredit {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else RealCoin.credit (innerBias (σ.next h).bias (σ.height - 2)) F +
    ofReal (calls (σ.next h).bias (σ.height - 2)) * (2 * ε)

def walkCredit {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then ∫⁻ z, selectorCredit σ h F ε z ∂RealCoin.law (σ.selector h) else F false

/-- The outer composition preserves linear credit; subcritical offspring finance amplification. -/
theorem expectation {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, walkCredit σ h F ε b ∂RealCoin.law (σ.walkBias h) ≤
      RealCoin.credit σ.bias F + ε := by
  have hinner := mixture_credit 1 (innerBias (σ.next h).bias (σ.height - 2)) (σ.selector h) F
  have houter := mixture_credit
    (CoinConditional.bias 1 (innerBias (σ.next h).bias (σ.height - 2)) (σ.selector h))
    0 (σ.walkBias h) F
  simp only [coin_credit_one] at hinner
  simp only [coin_credit_zero] at houter
  rw [← hinner, σ.outer_bias h] at houter
  have hq := sub_nonneg.mpr (σ.selector h).2.2
  have hc := calls_nonneg (σ.next h).bias (σ.height - 2)
  have hcost : ofReal (σ.walkBias h : ℝ) * ofReal (1 - (σ.selector h : ℝ)) *
      ofReal (calls (σ.next h).bias (σ.height - 2)) * 2 ≤ 1 := by
    have hm := σ.expected_calls_bound h
    have hb := ENNReal.ofReal_le_ofReal (show
        (σ.walkBias h : ℝ) * (1 - (σ.selector h : ℝ)) *
          calls (σ.next h).bias (σ.height - 2) * 2 ≤ 1 by linarith)
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (σ.walkBias h).2.1 hq) hc),
      ENNReal.ofReal_mul (mul_nonneg (σ.walkBias h).2.1 hq),
      ENNReal.ofReal_mul (σ.walkBias h).2.1, ENNReal.ofReal_one] at hb
    norm_num at hb ⊢
    exact hb
  calc
    _ = RealCoin.credit (σ.walkBias h) (fun b => if b then
        RealCoin.credit (σ.selector h)
          (fun z => if z then F true else RealCoin.credit
            (innerBias (σ.next h).bias (σ.height - 2)) F)
        else F false) +
        (ofReal (σ.walkBias h : ℝ) * ofReal (1 - (σ.selector h : ℝ)) *
          ofReal (calls (σ.next h).bias (σ.height - 2)) * 2) * ε := by
      simp only [RealCoin.lintegral_law, walkCredit, selectorCredit, RealCoin.credit,
        RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false]
      ring
    _ ≤ _ := by
      rw [houter]
      exact add_le_add le_rfl (mul_le_of_le_one_left (show 0 ≤ ε from zero_le) hcost)

end

end SampLib.LinearFactory
