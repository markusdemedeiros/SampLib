import SampLib.Samplers.ExpMinusRational
import SampLib.Samplers.OneDivOnePlus
import SampLib.Samplers.Complement
import Samplers.Bernoulli.Elementary

/-! # Logistic coins for signed rational inputs -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SigmoidRational

noncomputable section

/-- The logistic function of the rational input. -/
def bias (a b : ℤ) : unitInterval :=
  ⟨1 / (1 + Real.exp (-(a : ℝ) / b)), by positivity,
    (div_le_one (by positivity)).mpr (by linarith [Real.exp_pos (-(a : ℝ) / b)])⟩

private theorem positive_bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    OneDivOnePlus.bias (ExpMinusRational.bias a b ha hb) = bias a b := by
  apply Subtype.ext
  rfl

private theorem negative_bias (a b : ℤ) (ha : a < 0) (hb : 0 < b) :
    unitInterval.symm
      (OneDivOnePlus.bias (ExpMinusRational.bias (-a) b (neg_nonneg.mpr ha.le) hb)) = bias a b := by
  apply Subtype.ext
  simp only [unitInterval.coe_symm_eq, OneDivOnePlus.bias, EvenParity.bias,
    ExpMinusRational.bias, bias, Int.cast_neg, neg_neg]
  have he : Real.exp ((a : ℝ) / b) * Real.exp (-(a : ℝ) / b) = 1 := by
    rw [← Real.exp_add, show (a : ℝ) / b + -(a : ℝ) / b = 0 by ring, Real.exp_zero]
  simp only [neg_div] at he
  field_simp
  nlinarith

/-- Reflecting a negative input complements the logistic coin. -/
private theorem negative_expectation (a b : ℤ) (ha : a < 0) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ r, F (!r) ∂RealCoin.law
      (OneDivOnePlus.bias (ExpMinusRational.bias (-a) b (neg_nonneg.mpr ha.le) hb)) =
      ∫⁻ r, F r ∂RealCoin.law (bias a b) := by
  rw [Complement.expectation_preservation, Complement.law, negative_bias a b ha hb]

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

private theorem oneDiv_lc {rT : Type _} :
    (Occil.oneDivOnePlus : Exp rT).IsLocallyClosed := by is_lc

private theorem oneDiv_fv {rT : Type _} : (Occil.oneDivOnePlus : Exp rT).fv = ∅ := by
  simp [Occil.oneDivOnePlus, Exp.fv, FairCoin.fairCoin_fv]

@[local simp] private theorem oneDiv_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.oneDivOnePlus = Occil.oneDivOnePlus :=
  (Exp.open_lc k e _ oneDiv_lc).symm

@[local simp] private theorem oneDiv_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.oneDivOnePlus : Exp rT) = Occil.oneDivOnePlus :=
  Exp.closeRec_fresh x _ k (by simp [oneDiv_fv])

theorem sigmoidRational_lc {rT : Type _} :
    (Occil.FactoryExtra.sigmoidRational : Exp rT).IsLocallyClosed := by is_lc

theorem sigmoidRational_fv {rT : Type _} :
    (Occil.FactoryExtra.sigmoidRational : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.sigmoidRational, Exp.fv, oneDiv_fv,
    ExpMinusRational.expMinusRational_fv]

@[simp] theorem sigmoidRational_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.sigmoidRational = Occil.FactoryExtra.sigmoidRational :=
  (Exp.open_lc k e _ sigmoidRational_lc).symm

@[simp] theorem sigmoidRational_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.sigmoidRational : Exp rT) =
      Occil.FactoryExtra.sigmoidRational :=
  Exp.closeRec_fresh x _ k (by simp [sigmoidRational_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def exponentialCoin (a b : ℤ) : Val rT :=
  ⟨pl(fun u, &Occil.expMinusRational #int a #int b #()), .lam (by is_lc), by is_lc⟩

private theorem exponentialCoin_spec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin a b).fst #())
      (RealCoin.law (ExpMinusRational.bias a b ha hb)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [ExpMinusRational.expMinusRational_openRec,
      ExpMinusRational.expMinusRational_closeRec]
    iapply (ExpMinusRational.expMinusRational_distSpec E a b ha hb).spec F hF $$ Hcredit

private def negativeExponentialCoin (a b : ℤ) : Val rT :=
  ⟨pl(fun u, &Occil.expMinusRational (-#int a) #int b #()), .lam (by is_lc), by is_lc⟩

private theorem negativeExponentialCoin_spec (E : CoPset) (a b : ℤ)
    (ha : a < 0) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&(negativeExponentialCoin a b).fst #())
      (RealCoin.law (ExpMinusRational.bias (-a) b (neg_nonneg.mpr ha.le) hb)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ExpMinusRational.expMinusRational_openRec,
      ExpMinusRational.expMinusRational_closeRec, Exp.ofVal]
    iapply (ExpMinusRational.expMinusRational_distSpec E (-a) b (neg_nonneg.mpr ha.le) hb).spec F hF
      $$ Hcredit

/-- Execute the signed branch, then apply the reciprocal factory. -/
theorem twp_sigmoidRational (E : CoPset) (a b : ℤ) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias a b)) -∗
      tglWp E pl(&Occil.FactoryExtra.sigmoidRational #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  twp_pures
  rw [decide_eq_false (not_le.mpr hb)]
  twp_pures
  by_cases ha : a < 0
  · rw [decide_eq_true ha]
    twp_pure
    simp only [oneDiv_open, oneDiv_close, ExpMinusRational.expMinusRational_openRec,
      ExpMinusRational.expMinusRational_closeRec]
    twp_bind pl(&Occil.oneDivOnePlus &(negativeExponentialCoin a b).fst #())
    isimp only [← negative_expectation a b ha hb F] at Hcredit
    iapply ((OneDivOnePlus.oneDivOnePlus_distSpec E
      (ExpMinusRational.bias (-a) b (neg_nonneg.mpr ha.le) hb) (negativeExponentialCoin a b)
      (negativeExponentialCoin_spec E a b ha hb)).wp
      (fun r => F (!r)) (measurable_of_countable _) _) $$ Hcredit
    iintro %r Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !r
    iframe Hcredit
    ipureintro
    simp [Val.ext_iff, bool_not]
  · have ha0 : 0 ≤ a := not_lt.mp ha
    rw [decide_eq_false ha]
    twp_pure
    simp only [oneDiv_open, oneDiv_close, ExpMinusRational.expMinusRational_openRec,
      ExpMinusRational.expMinusRational_closeRec]
    isimp only [← positive_bias a b ha0 hb] at Hcredit
    have hrecip := OneDivOnePlus.oneDivOnePlus_distSpec (GF := GF) E
      (ExpMinusRational.bias a b ha0 hb) (exponentialCoin (rT := rT) a b)
      (exponentialCoin_spec E a b ha0 hb)
    simp [exponentialCoin, Exp.close, Exp.closeRec] at hrecip
    iapply hrecip.spec F (measurable_of_countable _) $$ Hcredit

theorem sigmoidRational_distSpec (E : CoPset) (a b : ℤ) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.sigmoidRational #int a #int b #())
      (RealCoin.law (bias a b)) Val.bool where
  spec F _ := wand_entails (twp_sigmoidRational E a b hb F)

end specification

end

end SampLib.SigmoidRational
