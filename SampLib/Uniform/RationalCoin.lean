import SampLib.Uniform.RealCoin
import SampLib.Uniform.Laws.RationalCoin
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # Exact rational Bernoulli sampling -/

open Set ProbLang Finset
open scoped ENNReal

namespace SampLib.RationalCoin

noncomputable section

private theorem valid_test (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) :
    Bool.or (Bool.or (decide (b ≤ 0)) (decide (a < 0))) (decide (b < a)) = false := by
  simp [not_le.mpr hb, not_lt.mpr ha, not_lt.mpr hab]

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
