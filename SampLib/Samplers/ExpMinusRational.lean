import SampLib.Distributions.AlternatingFactorial
import SampLib.Samplers.RationalCoin
import SampLib.Samplers.CoinProduct
import SampLib.Samplers.IterateCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Exact rational negative-exponential coins

Parity at the first failed factorial trial gives `exp(-t)` on the unit interval.
The integer part is a finite product of independent `exp(-1)` trials.
-/

open Set ProbLang
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.ExpMinusRational

noncomputable section

set_option maxHeartbeats 1200000

/-- The negative exponential of a nonnegative rational. -/
def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  ⟨Real.exp (-(a : ℝ) / b), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast neg_nonpos.mpr ha)
      (by exact_mod_cast hb.le))⟩

/-- Integer and fractional parts factor the rational exponential. -/
private theorem split_bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IterateCoin.bias (bias 1 1 (by decide) (by decide)) (a / b).toNat *
      bias (a % b) b (Int.emod_nonneg _ hb.ne') hb = bias a b ha hb := by
  apply Subtype.ext
  simp only [Set.Icc.coe_mul, IterateCoin.bias, bias, Int.cast_one, div_one]
  change Real.exp (-1) ^ (a / b).toNat * Real.exp (-(a % b : ℤ) / (b : ℝ)) =
    Real.exp (-(a : ℝ) / b)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hq : 0 ≤ a / b := Int.ediv_nonneg ha hb.le
  have hqcast : ((a / b).toNat : ℝ) = ((a / b : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hq
  have hsplit : (b : ℝ) * (a / b : ℤ) + (a % b : ℤ) = a := by
    exact_mod_cast Int.mul_ediv_add_emod a b
  rw [hqcast]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  nlinarith

private def outerCredit (a b : ℤ) (_ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) : Bool → ℝ≥0∞ :=
  CoinProduct.firstCredit (bias (a % b) b (Int.emod_nonneg _ hb.ne') hb) F

private theorem outer_expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    IterateCoin.credit (bias 1 1 (by decide) (by decide)) (a / b).toNat
      (outerCredit a b ha hb F) = RealCoin.credit (bias a b ha hb) F := by
  rw [IterateCoin.credit, ← RealCoin.lintegral_law, outerCredit]
  rw [CoinProduct.expectation_preservation, CoinProduct.law, split_bias]
  rw [RealCoin.lintegral_law]

private def trialBias (t : unitInterval) (i : ℕ) (hi : 1 ≤ i) : unitInterval :=
  ⟨(t : ℝ) / i, div_nonneg t.2.1 (Nat.cast_nonneg _), by
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
    exact (div_le_one (by positivity)).mpr (t.2.2.trans hiR)⟩

private def coinCredit (t : unitInterval) (i : ℕ) (F : Bool → ℝ≥0∞)
    (b : Bool) (ε : ℝ≥0∞) (r : Bool) : ℝ≥0∞ :=
  if r then AlternatingFactorial.credit t (i + 1) F (!b) + 2 * ε else F b

/-- The factorial recurrence preserves distribution credit; from step two, at
most half the probability continues, so doubling funds termination. -/
private theorem expectation (t : unitInterval) (i : ℕ) (hi : 2 ≤ i)
    (F : Bool → ℝ≥0∞) (b : Bool) (ε : ℝ≥0∞) :
    RealCoin.credit (trialBias t i (by omega)) (coinCredit t i F b ε) ≤
      AlternatingFactorial.credit t i F b + ε := by
  have hq : ofReal ((t : ℝ) / i) * 2 ≤ 1 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (div_nonneg t.2.1 (Nat.cast_nonneg _))]
    apply ENNReal.ofReal_le_one.mpr
    have hiR : (2 : ℝ) ≤ i := by exact_mod_cast hi
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < i)).mpr
    nlinarith [t.2.2]
  rw [AlternatingFactorial.credit_step]
  simp only [RealCoin.credit, RealCoin.pmf, trialBias, coinCredit,
    Bool.false_eq_true, ite_true, ite_false, AlternatingFactorial.hazard]
  calc
    _ = ofReal (1 - (t : ℝ) / i) * F b +
        ofReal ((t : ℝ) / i) * AlternatingFactorial.credit t (i + 1) F (!b) +
        (ofReal ((t : ℝ) / i) * 2) * ε := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hq)

private theorem first_expectation (t : unitInterval) (i : ℕ) (hi : 1 ≤ i)
    (F : Bool → ℝ≥0∞) (b : Bool) :
    RealCoin.credit (trialBias t i hi) (coinCredit t i F b 0) =
      AlternatingFactorial.credit t i F b := by
  rw [AlternatingFactorial.credit_step]
  simp [RealCoin.credit, RealCoin.pmf, trialBias, coinCredit,
    AlternatingFactorial.hazard, add_comm]

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

private def trial {rT : Type _} (a b : ℤ) : Exp rT := pl%
  rec go i parity :=
    if &Occil.rationalCoin #int a (#int b * i) then go (i + #1) (~parity)
    else parity

private def small {rT : Type _} : Exp rT := pl%
  fun numerator denominator,
    let loop := (rec go i parity :=
      if &Occil.rationalCoin numerator (denominator * i) then go (i + #1) (~parity)
      else parity);
    loop #1 #true

private theorem small_lc {rT : Type _} : (small : Exp rT).IsLocallyClosed := by is_lc

private theorem small_fv {rT : Type _} : (small : Exp rT).fv = ∅ := by
  simp [small, Exp.fv, RationalCoin.rationalCoin_fv]

@[local simp] private theorem small_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e small = small := (Exp.open_lc k e _ small_lc).symm

@[local simp] private theorem small_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (small : Exp rT) = small :=
  Exp.closeRec_fresh x _ k (by simp [small_fv])

private def whole {rT : Type _} : Exp rT := pl%
  rec rep n := if n = #0 then #true else
    if &small #1 #1 then rep (n - #1) else #false

/-- Closedness preserves the named sampler when it is used as a callback. -/
theorem expMinusRational_lc {rT : Type _} :
    (Occil.expMinusRational : Exp rT).IsLocallyClosed := by is_lc

theorem expMinusRational_fv {rT : Type _} :
    (Occil.expMinusRational : Exp rT).fv = ∅ := by
  simp [Occil.expMinusRational, Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem expMinusRational_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.expMinusRational = Occil.expMinusRational :=
  (Exp.open_lc k e _ expMinusRational_lc).symm

@[simp] theorem expMinusRational_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.expMinusRational : Exp rT) = Occil.expMinusRational :=
  Exp.closeRec_fresh x _ k (by simp [expMinusRational_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem denominator_valid (a b : ℤ) (hb : 0 < b) (hab : a ≤ b)
    (i : ℕ) (hi : 1 ≤ i) : 0 < b * i ∧ a ≤ b * i := by
  have hiZ : (1 : ℤ) ≤ i := by exact_mod_cast hi
  constructor <;> nlinarith

private theorem rational_trial_spec (E : CoPset) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (i : ℕ) (hi : 1 ≤ i) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int a #int (b * i))
      (RealCoin.law (trialBias (RationalCoin.bias a b ha hb hab) i hi)) Val.bool := by
  have hv := denominator_valid a b hb hab i hi
  have he : RationalCoin.bias a (b * i) ha hv.1 hv.2 =
      trialBias (RationalCoin.bias a b ha hb hab) i hi := by
    apply Subtype.ext
    simp only [RationalCoin.bias, trialBias, Int.cast_mul, Int.cast_natCast]
    rw [div_mul_eq_div_div]
  simpa only [he] using RationalCoin.rationalCoin_distSpec (GF := GF) E a (b * i) ha hv.1 hv.2

/-- Once the denominator is at least two, every round has a uniform exit chance. -/
private theorem twp_trial_tail (E : CoPset) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (i : ℕ) (hi : 2 ≤ i)
    (parity : Bool) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (AlternatingFactorial.credit (RationalCoin.bias a b ha hb hab) i F parity) -∗
      tglWp E pl(&(trial a b) #int (i : ℤ) #bool parity)
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %i %hi %parity Hcredit
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %i %hi %parity Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  have hi1 : 1 ≤ i := by omega
  iterate 4 twp_pure
  simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.rationalCoin #int a #int (b * i))
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken
    (expectation (RationalCoin.bias a b ha hb hab) i hi F parity ε) $$ Htotal
  isimp only [← RealCoin.lintegral_law] at Hsample
  iapply ((rational_trial_spec E a b ha hb hab i hi1).wp
    (coinCredit (RationalCoin.bias a b ha hb hab) i F parity ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists parity
    isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iterate 3 twp_pure
    isimp only [coinCredit, ite_true] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    rw [← Nat.cast_add_one]
    simp only [bool_not]
    twp_bind pl(&(trial a b) #int ((i + 1 : ℕ) : ℤ) #bool (!parity))
    iapply (tglWp_mono fun _ => tglWp_value)
    have hinext : 2 ≤ i + 1 := by omega
    iapply IH $$ Hterm %(i + 1) %hinext %(!parity) Hcredit

/-- The first denominator may be one; after one continuation the tail is uniformly bounded. -/
private theorem twp_trial (E : CoPset) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (i : ℕ) (hi : 1 ≤ i)
    (parity : Bool) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (AlternatingFactorial.credit (RationalCoin.bias a b ha hb hab) i F parity) -∗
      tglWp E pl(&(trial a b) #int (i : ℤ) #bool parity)
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  iterate 4 twp_pure
  simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.rationalCoin #int a #int (b * i))
  isimp only [← first_expectation (RationalCoin.bias a b ha hb hab) i hi F parity,
    ← RealCoin.lintegral_law] at Hcredit
  iapply ((rational_trial_spec E a b ha hb hab i hi).wp
    (coinCredit (RationalCoin.bias a b ha hb hab) i F parity 0)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %r Hcredit
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists parity
    isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iterate 3 twp_pure
    isimp only [coinCredit, ite_true, mul_zero, add_zero] at Hcredit
    rw [← Nat.cast_add_one]
    simp only [bool_not]
    twp_bind pl(&(trial a b) #int ((i + 1 : ℕ) : ℤ) #bool (!parity))
    iapply (tglWp_mono fun _ => tglWp_value)
    have hinext : 2 ≤ i + 1 := by omega
    iapply twp_trial_tail E a b ha hb hab (i + 1) hinext (!parity) F
    iexact Hcredit

private theorem twp_small (E : CoPset) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b ha hb) F) -∗
      tglWp E pl(&small #int a #int b)
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hcredit : RealCoin.credit (bias a b ha hb) F =
      AlternatingFactorial.credit (RationalCoin.bias a b ha hb hab) 1 F true := by
    rw [AlternatingFactorial.credit_one]
    simp [RealCoin.credit, RealCoin.pmf, bias, RationalCoin.bias, neg_div]
  have htrial := twp_trial (rT := rT) (GF := GF) E a b ha hb hab 1 (by decide) true F
  simp [trial, Exp.close, Exp.closeRec] at htrial
  iintro Hcredit
  isimp only [hcredit] at Hcredit
  iterate 3 twp_pure
  simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
  iapply htrial
  iexact Hcredit

private theorem twp_whole (E : CoPset) (n : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (IterateCoin.credit (bias 1 1 (by decide) (by decide)) n F) -∗
      tglWp E pl(&whole #int (n : ℤ))
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [IterateCoin.credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    have hwhole := IH F
    simp [whole, Exp.close, Exp.closeRec] at hwhole
    iintro Hcredit
    iterate 4 twp_pure
    simp only [small_open, small_close]
    twp_bind pl(&small #1 #1)
    isimp only [← IterateCoin.expectation, RealCoin.lintegral_law] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply twp_small E 1 1 (by decide) (by decide) (by decide)
        (IterateCoin.continuation (bias 1 1 (by decide) (by decide)) n F)
      iexact Hcredit
    iintro %v ⟨%r, %hv, Hcredit⟩
    subst v
    cases r
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [IterateCoin.continuation, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · iterate 2 twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      isimp only [IterateCoin.continuation, ite_true] at Hcredit
      iapply hwhole
      iexact Hcredit

private theorem valid_test (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    Bool.or (decide (a < 0)) (decide (b ≤ 0)) = false := by
  simp [not_lt.mpr ha, not_le.mpr hb]

/-- CTE execution: draw the integer-part product, then the remainder trial. -/
theorem twp_expMinusRational (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b ha hb) F) -∗
      tglWp E pl(&Occil.expMinusRational #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hq : ((a / b).toNat : ℤ) = a / b :=
    Int.toNat_of_nonneg (Int.ediv_nonneg ha hb.le)
  have hw := twp_whole (rT := rT) (GF := GF) E (a / b).toNat (outerCredit a b ha hb F)
  rw [hq] at hw
  have hs := twp_small (rT := rT) (GF := GF) E (a % b) b
    (Int.emod_nonneg _ hb.ne') hb (Int.emod_lt_of_pos a hb).le F
  simp [small, Exp.close, Exp.closeRec] at hs
  iintro Hcredit
  twp_pures
  rw [valid_test a b ha hb]
  iterate 4 twp_pure
  simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
  twp_bind pl(&whole #int (a / b))
  iapply tglWp_wand
  isplitl [Hcredit]
  · isimp only [← outer_expectation a b ha hb F] at Hcredit
    iapply hw
    iexact Hcredit
  iintro %v ⟨%r, %hv, Hcredit⟩
  subst v
  cases r
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [outerCredit, CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iterate 2 twp_pure
    isimp only [outerCredit, CoinProduct.firstCredit, ite_true,
      RealCoin.lintegral_law] at Hcredit
    isimp only [Exp.ofVal]
    iapply hs
    iexact Hcredit

/-- Exact Bernoulli law for every nonnegative rational argument. -/
theorem expMinusRational_distSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.expMinusRational #int a #int b #())
      (RealCoin.law (bias a b ha hb)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_expMinusRational E a b ha hb F)

end specification

end

end SampLib.ExpMinusRational
