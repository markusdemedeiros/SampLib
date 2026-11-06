import SampLib.Bernoulli.Laws.ExpMinusRational
import SampLib.Bernoulli.Syntax.ExpMinusRational
import SampLib.Uniform.RationalCoin
import SampLib.Bernoulli.CoinProduct
import SampLib.Continuous.IterateCoin
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

attribute [local simp] small_open small_close

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

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
