import SampLib.Core.SamplerStep
import SampLib.Bernoulli.Laws.BernoulliRetry
import SampLib.Uniform.UniformInt
import Samplers.Bernoulli.Rational
import Metrology.Iris.LocalBI

/-! # Reciprocal affine factory

A uniform rank selects a successful exit, an unsuccessful exit, or an input-coin
trial. The three interval widths identify the normalized reciprocal affine law.
-/

open Set ProbLang Finset
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.ReciprocalAffine

set_option maxHeartbeats 500000

noncomputable section

private theorem denominator_pos (p : unitInterval) (c s : ℕ) (hc : 0 < c) :
    0 < (c : ℝ) + s * (p : ℝ) :=
  add_pos_of_pos_of_nonneg (by exact_mod_cast hc) (mul_nonneg (Nat.cast_nonneg s) p.2.1)

/-- Bias `d/(c+s*p)` for disjoint integer exit widths `d≤c`. -/
def bias (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c) : unitInterval :=
  ⟨(d : ℝ) / ((c : ℝ) + s * (p : ℝ)),
    div_nonneg (Nat.cast_nonneg d) (denominator_pos p c s hc).le,
    (div_le_one (denominator_pos p c s hc)).mpr (by
      have hdc : (d : ℝ) ≤ c := by exact_mod_cast hd
      exact hdc.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) p.2.1)))⟩

/-- Probability of selecting the input interval and observing a failure. -/
def retry (p : unitInterval) (c s : ℕ) (hc : 0 < c) : unitInterval :=
  ⟨s * (1 - (p : ℝ)) / (c + s),
    div_nonneg (mul_nonneg (Nat.cast_nonneg s) (sub_nonneg.mpr p.2.2)) (by positivity),
    (div_le_one (by positivity : (0 : ℝ) < c + s)).mpr (by
      have hcR : (0 : ℝ) < c := by exact_mod_cast hc
      nlinarith [mul_nonneg (Nat.cast_nonneg s) p.2.1])⟩

@[simp] private theorem retry_coe (p : unitInterval) (c s : ℕ) (hc : 0 < c) :
    (retry p c s hc : ℝ) = s * (1 - (p : ℝ)) / (c + s) := rfl

private theorem retry_lt_one (p : unitInterval) (c s : ℕ) (hc : 0 < c) :
    (retry p c s hc : ℝ) < 1 := by
  change (s : ℝ) * (1 - (p : ℝ)) / (c + s) < 1
  rw [div_lt_one (by positivity : (0 : ℝ) < c + s)]
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  nlinarith [mul_nonneg (Nat.cast_nonneg s) p.2.1]

/-- Credit after the input coin, with amplified credit on its retry branch. -/
def coinCredit (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else RealCoin.credit (bias p c d s hc hd) F +
    BernoulliRetry.factor (retry p c s hc) * ε

/-- Credit assigned to a rank in the three consecutive intervals. -/
def rankCredit (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < d then F true else if k < c then F false else
    ∫⁻ b, coinCredit p c d s hc hd F ε b ∂RealCoin.law p

private theorem rank_partition (c d s : ℕ) (hd : d ≤ c) (A B C : ℝ≥0∞) :
    ∑ k ∈ range (c + s), (if k < d then A else if k < c then B else C) =
      d * A + ((c - d : ℕ) : ℝ≥0∞) * B + s * C := by
  have hsum : c + s = d + ((c - d) + s) := by omega
  rw [hsum, sum_range_add, sum_range_add]
  have hfirst : (∑ k ∈ range d, if k < d then A else if k < c then B else C) = d * A := by
    calc
      _ = ∑ k ∈ range d, A := sum_congr rfl fun k hk => by simp [mem_range.mp hk]
      _ = _ := by simp [nsmul_eq_mul]
  have hsecond : (∑ k ∈ range (c - d),
      if d + k < d then A else if d + k < c then B else C) = ((c - d : ℕ) : ℝ≥0∞) * B := by
    calc
      _ = ∑ k ∈ range (c - d), B := sum_congr rfl fun k hk => by
        have hk' := mem_range.mp hk
        simp [show ¬d + k < d by omega, show d + k < c by omega]
      _ = _ := by simp [nsmul_eq_mul]
  rw [hfirst, hsecond]
  simp [show ∀ k : ℕ, ¬d + (c - d + k) < d by omega,
    show ∀ k : ℕ, ¬d + (c - d + k) < c by omega, nsmul_eq_mul, add_assoc]

/-- The three interval widths balance the reciprocal law and fund retries. -/
theorem expectation (p : unitInterval) (c d s : ℕ) (hc : 0 < c) (hd : d ≤ c)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ k ∈ range (c + s), rankCredit p c d s hc hd F ε k) / ((c + s : ℕ) : ℝ≥0∞) ≤
      RealCoin.credit (bias p c d s hc hd) F + ε := by
  let a : ℝ := d / (c + s)
  let b : ℝ := ((c - d : ℕ) + s * (p : ℝ)) / (c + s)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b :=
    div_nonneg (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) p.2.1))
      (by positivity)
  have hsum : a + b + (retry p c s hc : ℝ) = 1 := by
    dsimp [a, b, retry]
    rw [Nat.cast_sub hd]
    field_simp
    ring
  have hnormalized : BernoulliRetry.bias a b ha hb = bias p c d s hc hd := by
    apply Subtype.ext
    change a / (a + b) = (d : ℝ) / ((c : ℝ) + s * (p : ℝ))
    have hT : (c : ℝ) + s ≠ 0 := by positivity
    have hab : a + b = ((c : ℝ) + s * (p : ℝ)) / (c + s) := by
      dsimp [a, b]
      rw [Nat.cast_sub hd]
      ring
    rw [hab]
    exact div_div_div_cancel_right₀ hT _ _
  have h := BernoulliRetry.expectation a b ha hb (retry p c s hc)
    (retry_lt_one p c s hc) hsum F ε
  rw [hnormalized] at h
  calc
    _ = ofReal a * F true + ofReal b * F false + ofReal (retry p c s hc : ℝ) *
        (RealCoin.credit (bias p c d s hc hd) F +
          BernoulliRetry.factor (retry p c s hc) * ε) := by
      simp only [rankCredit, Nat.cast_add]
      rw [rank_partition c d s hd]
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, coinCredit,
        ite_true, Bool.false_eq_true, ite_false]
      dsimp [a, b]
      simp only [ENNReal.ofReal_div_of_pos
        (by positivity : (0 : ℝ) < c + s)]
      rw [ofReal_add (Nat.cast_nonneg (c - d)) (mul_nonneg (Nat.cast_nonneg s) p.2.1)]
      simp only [ofReal_add (Nat.cast_nonneg c) (Nat.cast_nonneg s),
        ofReal_mul (Nat.cast_nonneg s), ENNReal.ofReal_natCast,
        ENNReal.div_eq_inv_mul]
      ring
    _ ≤ _ := h


@[simp] theorem reciprocalAffine_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.reciprocalAffine = Occil.FactoryExtra.reciprocalAffine :=
  (Exp.open_lc k e _ (by is_lc)).symm

@[simp] theorem reciprocalAffine_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.reciprocalAffine : Exp rT) =
      Occil.FactoryExtra.reciprocalAffine :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.reciprocalAffine, Exp.fv, UniformInt.uniformInt_fv])

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.reciprocalAffine, .fix (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.reciprocalAffine := rfl

private theorem valid_guard (a b y : ℕ) (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) :
    (((decide ((a : ℤ) ≤ 0) || decide ((b : ℤ) ≤ 0)) || false) ||
      decide ((y : ℤ) ≤ 0)) = false := by
  simp [show a ≠ 0 by omega, show b ≠ 0 by omega, show y ≠ 0 by omega]


private theorem bound_guard (a b x y : ℕ) (h : x * b ≤ a * y) :
    decide ((a : ℤ) * y < (x : ℤ) * b) = false :=
  decide_eq_false (by exact_mod_cast not_lt.mpr h)


section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The affine denominator is positive for every input bias, including both endpoints. -/
theorem twp_reciprocalAffine (E : CoPset) (p : unitInterval) (a b x y : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hbound : x * b ≤ a * y) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p (a * y) (x * b) (b * y) (Nat.mul_pos ha hy) hbound) F) -∗
      tglWp E pl(&Occil.FactoryExtra.reciprocalAffine &coin.fst
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hc := Nat.mul_pos ha hy
  have ht := Nat.add_pos_left hc (b * y)
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (BernoulliRetry.one_lt_factor (retry p (a * y) (b * y) hc)
      (retry_lt_one p (a * y) (b * y) hc)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  rw [← source_fst (rT := rT)]
  iterate 7 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
    Var.internal.injEq, ProbLang.openRec_val_fst, UniformInt.uniformInt_openRec,
    UniformInt.uniformInt_closeRec])
  twp_pures
  rw [valid_guard a b y ha hb hy]
  twp_pures
  rw [bound_guard a b x y hbound]
  twp_pure
  simp only [UniformInt.uniformInt_openRec]
  twp_pure
  simp only [← Int.natCast_mul, ← Int.natCast_add]
  twp_bind pl(&Occil.uniformInt #int ((a * y + b * y : ℕ) : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation p (a * y) (x * b) (b * y) hc hbound F ε)
    $$ Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E (a * y + b * y) ht
      (rankCredit p (a * y) (x * b) (b * y) hc hbound F ε)) $$ Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_pures
  simp only [Int.ofNat_lt]
  by_cases hd : k < x * b
  · rw [decide_eq_true hd]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [rankCredit, ite_eq_left hd] at Hcredit
    iframe Hcredit
    itrivial
  · rw [decide_eq_false hd]
    iterate 2 twp_pure
    simp only [Int.ofNat_lt]
    by_cases hkc : k < a * y
    · rw [decide_eq_true hkc]
      twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [rankCredit, ite_eq_right hd, ite_eq_left hkc] at Hcredit
      iframe Hcredit
      itrivial
    · rw [decide_eq_false hkc]
      twp_pure
      twp_bind pl(&coin.fst #())
      isimp only [rankCredit, ite_eq_right hd, ite_eq_right hkc] at Hcredit
      iapply (hcoin.wp (coinCredit p (a * y) (x * b) (b * y) hc hbound F ε)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %r Hcredit
      cases r
      · twp_pure
        isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(source (rT := rT)).fst &coin.fst
          #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm Hcredit
      · twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [coinCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial

/-- Exact reciprocal affine law for every valid rational input. -/
theorem reciprocalAffine_distSpec (E : CoPset) (p : unitInterval) (a b x y : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hbound : x * b ≤ a * y) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.reciprocalAffine &coin.fst
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
      (RealCoin.law (bias p (a * y) (x * b) (b * y) (Nat.mul_pos ha hy) hbound)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_reciprocalAffine E p a b x y ha hb hy hbound coin hcoin F)

end specification

end

end SampLib.ReciprocalAffine
