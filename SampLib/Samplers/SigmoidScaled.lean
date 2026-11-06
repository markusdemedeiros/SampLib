import SampLib.Samplers.ExpMinusScaled
import SampLib.Samplers.OneDivOnePlus
import SampLib.Samplers.Complement
import Samplers.Bernoulli.Elementary

/-! # Logistic factories for signed rational multiples of an input bias -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SigmoidScaled

noncomputable section

/-- The logistic function at `(a/b)*p`. -/
def bias (p : unitInterval) (a : ℤ) (b : ℕ) : unitInterval :=
  ⟨1 / (1 + Real.exp (-(a : ℝ) / b * (p : ℝ))), by positivity,
    (div_le_one (by positivity)).mpr (by linarith [Real.exp_pos (-(a : ℝ) / b * (p : ℝ))])⟩

private theorem positive_bias (p : unitInterval) (a : ℤ) (b : ℕ) (ha : 0 ≤ a) :
    OneDivOnePlus.bias (ExpMinusScaled.bias p a.toNat b) = bias p a b := by
  have hcast : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  apply Subtype.ext
  simp [OneDivOnePlus.bias, EvenParity.bias, ExpMinusScaled.bias, bias, hcast]

private theorem negative_bias (p : unitInterval) (a : ℤ) (b : ℕ) (ha : a < 0) :
    unitInterval.symm
      (OneDivOnePlus.bias (ExpMinusScaled.bias p (-a).toNat b)) = bias p a b := by
  have hcast : ((-a).toNat : ℝ) = -(a : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (neg_nonneg.mpr ha.le)
  apply Subtype.ext
  simp only [unitInterval.coe_symm_eq, OneDivOnePlus.bias, EvenParity.bias,
    ExpMinusScaled.bias, bias, hcast, neg_neg]
  have he : Real.exp ((a : ℝ) * (p : ℝ) / b) *
      Real.exp (-((a : ℝ) * (p : ℝ) / b)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp
  nlinarith

/-- Reflecting a negative input complements the logistic coin. -/
private theorem negative_expectation (p : unitInterval) (a : ℤ) (b : ℕ) (ha : a < 0)
    (F : Bool → ℝ≥0∞) :
    ∫⁻ r, F (!r) ∂RealCoin.law
      (OneDivOnePlus.bias (ExpMinusScaled.bias p (-a).toNat b)) =
      ∫⁻ r, F r ∂RealCoin.law (bias p a b) := by
  rw [Complement.expectation_preservation, Complement.law, negative_bias p a b ha]

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

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def exponentialCoin (coin : Val rT) (a : ℤ) (b : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.expMinusScaled &coin.fst #int a #int (b : ℤ) #()),
    .lam (by is_lc), by is_lc⟩

private theorem exponentialCoin_spec (E : CoPset) (p : unitInterval) (a : ℤ) (b : ℕ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin coin a b).fst #())
      (RealCoin.law (ExpMinusScaled.bias p a.toNat b)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [ExpMinusScaled.expMinusScaled_openRec]
    have hs := ExpMinusScaled.expMinusScaled_distSpec E p a.toNat b hb coin hcoin
    rw [Int.toNat_of_nonneg ha] at hs
    iapply hs.spec F hF $$ Hcredit

private def negativeExponentialCoin (coin : Val rT) (a : ℤ) (b : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.expMinusScaled &coin.fst (-#int a) #int (b : ℤ) #()),
    .lam (by is_lc), by is_lc⟩

private theorem negativeExponentialCoin_spec (E : CoPset) (p : unitInterval) (a : ℤ) (b : ℕ)
    (ha : a < 0) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(negativeExponentialCoin coin a b).fst #())
      (RealCoin.law (ExpMinusScaled.bias p (-a).toNat b)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ExpMinusScaled.expMinusScaled_openRec, Exp.ofVal]
    have hs := ExpMinusScaled.expMinusScaled_distSpec E p (-a).toNat b hb coin hcoin
    rw [Int.toNat_of_nonneg (neg_nonneg.mpr ha.le)] at hs
    iapply hs.spec F hF $$ Hcredit

/-- Execute the signed branch, then apply the reciprocal factory. -/
theorem twp_sigmoidScaled (E : CoPset) (p : unitInterval) (a : ℤ) (b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias p a b)) -∗
      tglWp E pl(&Occil.FactoryExtra.sigmoidScaled &coin.fst #int a #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  twp_pures
  by_cases ha : a < 0
  · rw [decide_eq_true ha]
    twp_pure
    simp only [oneDiv_open, oneDiv_close, ExpMinusScaled.expMinusScaled_openRec,
      ExpMinusScaled.expMinusScaled_closeRec]
    twp_bind pl(&Occil.oneDivOnePlus &(negativeExponentialCoin coin a b).fst #())
    isimp only [← negative_expectation p a b ha F] at Hcredit
    iapply ((OneDivOnePlus.oneDivOnePlus_distSpec E
      (ExpMinusScaled.bias p (-a).toNat b) (negativeExponentialCoin coin a b)
      (negativeExponentialCoin_spec E p a b ha hb coin hcoin)).wp
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
    simp only [oneDiv_open, oneDiv_close, ExpMinusScaled.expMinusScaled_openRec,
      ExpMinusScaled.expMinusScaled_closeRec]
    isimp only [← positive_bias p a b ha0] at Hcredit
    have hrecip := OneDivOnePlus.oneDivOnePlus_distSpec (GF := GF) E
      (ExpMinusScaled.bias p a.toNat b) (exponentialCoin coin a b)
      (exponentialCoin_spec E p a b ha0 hb coin hcoin)
    simp only [exponentialCoin] at hrecip
    iapply hrecip.spec F (measurable_of_countable _) $$ Hcredit

theorem sigmoidScaled_distSpec (E : CoPset) (p : unitInterval) (a : ℤ) (b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.sigmoidScaled &coin.fst #int a #int (b : ℤ) #())
      (RealCoin.law (bias p a b)) Val.bool where
  spec F _ := wand_entails (twp_sigmoidScaled E p a b hb coin hcoin F)

end specification

end

end SampLib.SigmoidScaled
