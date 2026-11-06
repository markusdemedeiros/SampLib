import SampLib.Distributions.AdaptivePowerCredit
import SampLib.Distributions.LinearFactory

/-! # Integer parameters of Huber's adaptive power walk

Each successful amplification multiplies the coefficient by beta and halves
the supplied margin. All arithmetic below follows the source integer formulas.
-/

open ProbLang
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.LinearPowerWalk

noncomputable section

structure Parameters (p : unitInterval) where
  a : ℤ
  b : ℤ
  e : ℤ
  f : ℤ
  a_pos : 0 < a
  b_pos : 0 < b
  e_pos : 0 < e
  e_lt_f : e < f
  bound : Gambler.ratio p a b ≤ 1 - (e : ℝ) / f

namespace Parameters

variable {p : unitInterval} (σ : Parameters p)

def margin : ℝ := (σ.e : ℝ) / σ.f

theorem f_pos : 0 < σ.f := σ.e_pos.trans σ.e_lt_f

theorem margin_pos : 0 < σ.margin :=
  div_pos (by exact_mod_cast σ.e_pos) (by exact_mod_cast σ.f_pos)

theorem margin_lt_one : σ.margin < 1 :=
  (div_lt_one (by exact_mod_cast σ.f_pos)).mpr (by exact_mod_cast σ.e_lt_f)

def bias : unitInterval :=
  ⟨Gambler.ratio p σ.a σ.b, Gambler.ratio_nonneg p σ.a σ.b σ.a_pos σ.b_pos,
    σ.bound.trans (sub_le_self _ σ.margin_pos.le)⟩

@[simp] theorem bias_coe : (σ.bias : ℝ) = Gambler.ratio p σ.a σ.b := rfl

def factorNum : ℤ := 2 * σ.f - σ.e

def factorDen : ℤ := 2 * (σ.f - σ.e)

theorem factorNum_pos : 0 < σ.factorNum := by
  have := σ.e_lt_f
  have := σ.f_pos
  dsimp [factorNum]
  omega

theorem factorDen_pos : 0 < σ.factorDen :=
  mul_pos (by norm_num) (sub_pos.mpr σ.e_lt_f)

theorem factor_le : σ.factorDen ≤ σ.factorNum := by
  have := σ.e_pos
  dsimp [factorNum, factorDen]
  omega

theorem factor_ratio : (σ.factorNum : ℝ) / σ.factorDen =
    AdaptivePowerWalk.amplification σ.margin := by
  have hf : (σ.f : ℝ) ≠ 0 := by exact_mod_cast σ.f_pos.ne'
  have hdiff : 0 < (σ.f : ℝ) - σ.e := by exact_mod_cast sub_pos.mpr σ.e_lt_f
  simp only [factorNum, factorDen, margin, AdaptivePowerWalk.amplification,
    Int.cast_mul, Int.cast_sub, Int.cast_ofNat]
  field_simp [hf, hdiff.ne']

private theorem next_ratio : Gambler.ratio p (σ.a * σ.factorNum) (σ.b * σ.factorDen) =
    (σ.bias : ℝ) * AdaptivePowerWalk.amplification σ.margin := by
  rw [← σ.factor_ratio]
  have hb : (σ.b : ℝ) ≠ 0 := by exact_mod_cast σ.b_pos.ne'
  simp only [Gambler.ratio, bias_coe, Int.cast_mul]
  field_simp

def next : Parameters p where
  a := σ.a * σ.factorNum
  b := σ.b * σ.factorDen
  e := σ.e
  f := 2 * σ.f
  a_pos := mul_pos σ.a_pos σ.factorNum_pos
  b_pos := mul_pos σ.b_pos σ.factorDen_pos
  e_pos := σ.e_pos
  e_lt_f := by have := σ.e_lt_f; have := σ.f_pos; omega
  bound := by
    rw [next_ratio]
    have h := AdaptivePowerWalk.amplification_margin σ.margin σ.bias σ.margin_lt_one σ.bound
    convert h using 1
    push_cast
    dsimp [margin]
    ring

@[simp] theorem next_margin : σ.next.margin = σ.margin / 2 := by
  simp only [next, margin, Int.cast_mul, Int.cast_ofNat]
  ring

theorem next_bias : (σ.next.bias : ℝ) =
    (σ.bias : ℝ) * AdaptivePowerWalk.amplification σ.margin := σ.next_ratio

def selectorBase : unitInterval :=
  RationalCoin.bias σ.factorDen σ.factorNum σ.factorDen_pos.le σ.factorNum_pos σ.factor_le

def selector (n : ℕ) : unitInterval := IterateCoin.bias σ.selectorBase n

theorem selector_coe (n : ℕ) : (σ.selector n : ℝ) =
    AdaptivePowerWalk.selection σ.margin n := by
  have hf : (σ.f : ℝ) ≠ 0 := by exact_mod_cast σ.f_pos.ne'
  have hn : 0 < 2 * (σ.f : ℝ) - σ.e := by exact_mod_cast σ.factorNum_pos
  simp only [selector, IterateCoin.bias, selectorBase, RationalCoin.bias,
    AdaptivePowerWalk.selection, factorNum, factorDen, margin,
    Int.cast_mul, Int.cast_sub, Int.cast_ofNat]
  congr 1
  field_simp [hf, hn.ne']

theorem threshold_iff (n : ℕ) :
    355 * σ.f < 100 * (n : ℤ) * σ.e ↔ 355 / 100 < (n : ℝ) * σ.margin := by
  have hf : 0 < (σ.f : ℝ) := by exact_mod_cast σ.f_pos
  rw [margin, ← mul_div_assoc, lt_div_iff₀ hf]
  have hc : 355 * (σ.f : ℝ) < 100 * (n : ℝ) * σ.e ↔
      355 / 100 * (σ.f : ℝ) < (n : ℝ) * σ.e := by constructor <;> intro h <;> nlinarith
  have hcast : 355 * σ.f < 100 * (n : ℤ) * σ.e ↔
      355 * (σ.f : ℝ) < 100 * (n : ℝ) * σ.e := by
    constructor <;> intro h <;> exact_mod_cast h
  exact hcast.trans hc

def credit (n : ℕ) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) : ℝ≥0∞ :=
  IterateCoin.credit σ.bias n F + ofReal (AdaptivePowerWalk.budget σ.margin n) * δ

theorem credit_eq (n : ℕ) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) :
    σ.credit n F δ = IterateCoin.credit σ.bias n F +
      ofReal (AdaptivePowerWalk.budget σ.margin n) * δ := rfl

@[simp] theorem credit_zero (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) : σ.credit 0 F δ = F true := by
  simp [credit, IterateCoin.credit_zero]

/-- The integer parameter updates instantiate the common power/work kernel. -/
theorem expectation (amplify : Bool) (n : ℕ) (hn : 0 < n)
    (hthreshold : if amplify then 355 / 100 < (n : ℝ) * σ.margin
      else (n : ℝ) * σ.margin ≤ 355 / 100)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) :
    (∫⁻ z, AdaptivePowerWalk.stepCredit amplify σ.margin σ.bias σ.next.bias n F δ z
      ∂RealCoin.law (AdaptivePowerWalk.drawBias amplify σ.bias (σ.selector n))) ≤
      σ.credit n F δ + δ :=
  AdaptivePowerWalk.expectation amplify σ.margin σ.margin_pos σ.margin_lt_one
    σ.bias σ.next.bias (σ.selector n) σ.bound n hn σ.next_bias (σ.selector_coe n)
    hthreshold F δ

def initialSlack (n : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  (ofReal (AdaptivePowerWalk.budget σ.margin n) + 1)⁻¹ * ε

theorem initialSlack_pos (n : ℕ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    0 < σ.initialSlack n ε := by
  apply ENNReal.mul_pos
  · exact ne_of_gt (ENNReal.inv_pos.mpr (by finiteness))
  · exact ne_of_gt hε

theorem initialSlack_budget (n : ℕ) (ε : ℝ≥0∞) :
    ofReal (AdaptivePowerWalk.budget σ.margin n) * σ.initialSlack n ε +
      σ.initialSlack n ε = ε := by
  calc
    _ = (ofReal (AdaptivePowerWalk.budget σ.margin n) + 1) * σ.initialSlack n ε := by ring
    _ = ε := ?_
  simp only [initialSlack]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

/-- The expanding branch inherits exactly the advertised linear-factory margin. -/
def ofAdmissible (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) : Parameters p where
  a := a
  b := b
  e := e
  f := f
  a_pos := h.2.1.trans hba
  b_pos := h.2.1
  e_pos := (h.2.2 hba).1
  e_lt_f := (h.2.2 hba).2.1
  bound := (h.2.2 hba).2.2

theorem ofAdmissible_bias (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) :
    (ofAdmissible p a b e f h hba).bias = LinearFactory.bias p a b e f h := by
  apply Subtype.ext
  rfl

end Parameters

end

end SampLib.LinearPowerWalk
