import SampLib.Samplers.RealCoin
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # Exact rational Bernoulli sampling -/

open Set ProbLang Finset
open ENNReal (ofReal ofReal_div_of_pos div_eq_inv_mul)
open scoped ENNReal

namespace SampLib.RationalCoin

noncomputable section

/-- The valid rational input, regarded as a probability. -/
def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) : unitInterval :=
  ⟨(a : ℝ) / (b : ℝ), div_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb.le),
    (div_le_one (by exact_mod_cast hb)).mpr (by exact_mod_cast hab)⟩

/-- Credit assigned to a uniform integer rank. -/
def rankCredit (a : ℤ) (F : Bool → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if (k : ℤ) < a then F true else F false

/-- Counting ranks below the threshold gives the rational Bernoulli expectation. -/
theorem expectation (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) :
    (∑ k ∈ range b.toNat, rankCredit a F k) / b.toNat =
      RealCoin.credit (bias a b ha hb hab) F := by
  have hab' : a.toNat ≤ b.toNat := by omega
  have hlt (k : ℕ) : (k : ℤ) < a ↔ k < a.toNat := by omega
  have hsum : (∑ k ∈ range b.toNat, rankCredit a F k) =
      (a.toNat : ℝ≥0∞) * F true + ((b.toNat - a.toNat : ℕ) : ℝ≥0∞) * F false := by
    simp only [rankCredit, hlt]
    conv_lhs => rw [← Nat.add_sub_of_le hab', sum_range_add]
    congr 1
    · calc
        _ = ∑ k ∈ range a.toNat, F true :=
          sum_congr rfl fun k hk => ite_eq_left (mem_range.mp hk)
        _ = _ := by simp [nsmul_eq_mul]
    · simp [Nat.not_lt.mpr (Nat.le_add_right a.toNat _), nsmul_eq_mul]
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have haCast : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  have hbCast : (b.toNat : ℝ) = (b : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hb.le
  have ht : ofReal ((a : ℝ) / b) =
      (a.toNat : ℝ≥0∞) / b.toNat := by
    rw [← haCast, ← hbCast,
      ofReal_div_of_pos (by exact_mod_cast (show 0 < b.toNat by omega))]
    simp
  have hc : (1 : ℝ) - (a : ℝ) / b = ((b.toNat - a.toNat : ℕ) : ℝ) / b.toNat := by
    rw [Nat.cast_sub hab', haCast, hbCast]
    field_simp
  have hf : ofReal (1 - (a : ℝ) / b) =
      ((b.toNat - a.toNat : ℕ) : ℝ≥0∞) / b.toNat := by
    rw [hc, ofReal_div_of_pos (by exact_mod_cast (show 0 < b.toNat by omega))]
    simp
  rw [hsum]
  simp only [RealCoin.credit, RealCoin.pmf, bias, Bool.false_eq_true, ite_true, ite_false, ht, hf,
    div_eq_inv_mul]
  ring

private theorem valid_test (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    Bool.or (Bool.or (decide (b ≤ 0)) (decide (a < 0))) (decide (b < a)) = false := by
  simp [not_le.mpr hb, not_lt.mpr ha, not_lt.mpr hab]

private theorem zero_credit (b : ℤ) (ha : (0 : ℤ) ≤ 0) (hb : 0 < b) (hab : 0 ≤ b)
    (F : Bool → ℝ≥0∞) : RealCoin.credit (bias 0 b ha hb hab) F = F false := by
  simp [RealCoin.credit, RealCoin.pmf, bias]

private theorem full_credit (b : ℤ) (ha : 0 ≤ b) (hb : 0 < b) (hab : b ≤ b)
    (F : Bool → ℝ≥0∞) : RealCoin.credit (bias b b ha hb hab) F = F true := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  simp [RealCoin.credit, RealCoin.pmf, bias, hbR]

private theorem rankCredit_eq (a : ℤ) (F : Bool → ℝ≥0∞) (k : ℕ) :
    rankCredit a F k = F (decide ((k : ℤ) < a)) := by
  by_cases h : (k : ℤ) < a <;> simp [rankCredit, h]

/-- Closedness rewrites preserve the named sampler inside callback bodies. -/
theorem rationalCoin_lc {rT : Type _} : (Occil.rationalCoin : Exp rT).IsLocallyClosed := by is_lc

theorem rationalCoin_fv {rT : Type _} : (Occil.rationalCoin : Exp rT).fv = ∅ := by
  simp [Occil.rationalCoin, Exp.fv]

@[simp] theorem rationalCoin_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.rationalCoin = Occil.rationalCoin :=
  (Exp.open_lc k e _ rationalCoin_lc).symm

@[simp] theorem rationalCoin_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.rationalCoin : Exp rT) = Occil.rationalCoin :=
  Exp.closeRec_fresh x _ k (by simp [rationalCoin_fv])

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification, including the deterministic probabilities zero and one. -/
theorem twp_rationalCoin (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a b ha hb hab) F) -∗
      tglWp E pl(&Occil.rationalCoin #int a #int b)
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  twp_pures
  rw [valid_test a b ha hb hab]
  twp_pures
  by_cases hz : a = 0
  · subst a
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [zero_credit] at Hcredit
    iframe Hcredit
    itrivial
  · rw [int_beq, beq_eq_false_iff_ne.mpr hz]
    twp_pures
    by_cases hf : a = b
    · subst a
      rw [int_beq, beq_self_eq_true]
      twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [full_credit] at Hcredit
      iframe Hcredit
      itrivial
    · rw [int_beq, beq_eq_false_iff_ne.mpr hf]
      twp_pures
      twp_bind pl(rand(#int b, #()))
      iapply (twp_rand_exp (ε₂ := rankCredit a F) hb ?_) $$ Hcredit
      · rw [expectation a b ha hb hab F]
      iintro %k ⟨%hk, Hcredit⟩
      twp_pures
      twp_value
      imodintro
      iexists (decide (k < a))
      isimp only [rankCredit_eq, Int.toNat_of_nonneg hk.1] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed Bernoulli law with bias `a / b`. -/
theorem rationalCoin_distSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int a #int b)
      (RealCoin.law (bias a b ha hb hab)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_rationalCoin E a b ha hb hab F)

end specification

end

end SampLib.RationalCoin
