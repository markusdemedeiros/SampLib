import SampLib.Distributions.GoldenFamily
import SampLib.Samplers.IntegerSign
import SampLib.Samplers.IterateCoin

/-! # Negative powers of the generalized golden root

The quadratic factors through the inverse root with a positive cofactor on the
unit interval. Independent repetitions then give `G(m,ell)^(-k)`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.GoldenFamily

noncomputable section

private theorem cofactor_pos (a : Parameters) (n den : ℕ) (hn : n ≤ den) (hd : 0 < den) :
    0 < (a.ell : ℝ) * n + ((a.m : ℝ) + (a.ell : ℝ) * (bias a : ℝ)) * den := by
  have hden : (0 : ℝ) < den := by exact_mod_cast hd
  have hp := bias_pos a
  rcases a.unit with h | h
  · have hm : (0 : ℝ) < a.m := by exact_mod_cast a.positive
    rw [h]
    norm_num
    positivity
  · have hm : (3 : ℝ) ≤ a.m := by exact_mod_cast a.minus h
    have hn' : (n : ℝ) ≤ den := by exact_mod_cast hn
    have hprod := mul_le_mul_of_nonneg_right hm hden.le
    have hprob := mul_lt_mul_of_pos_right (bias_lt_one a) hden
    rw [h]
    norm_num
    nlinarith

/-- The quadratic has the required sign throughout the oracle's unit-interval domain. -/
theorem polynomial_sign (a : Parameters) (n den : ℕ) (hn : n ≤ den) (hd : 0 < den) :
    (a.ell * (n : ℤ) * n + (a.m : ℤ) * n * den - (den : ℤ) * den).sign =
      AlgebraicRoot.side (bias a) (-1) n den := by
  apply IntegerSign.sign_of_right_factor (bias a) n den _
    ((a.ell : ℝ) * n + ((a.m : ℝ) + (a.ell : ℝ) * (bias a : ℝ)) * den)
    (cofactor_pos a n den hn hd)
  push_cast
  calc
    _ = (a.ell : ℝ) * (n : ℝ) ^ 2 + (a.m : ℝ) * n * den -
        ((a.ell : ℝ) * (bias a : ℝ) ^ 2 + (a.m : ℝ) * (bias a : ℝ)) * (den : ℝ) ^ 2 := by
      rw [bias_equation a]
      ring
    _ = _ := by ring

private def oracle {rT : Type _} (a : Parameters) : Val rT :=
  ⟨pl(fun n d, &Occil.Constants.integerSign
    (#int a.ell * n * n + #int (a.m : ℤ) * n * d - d * d)),
    .lam (by is_lc), by is_lc⟩

private def root {rT : Type _} (a : Parameters) : Val rT :=
  ⟨pl(fun u, &Occil.Constants.algebraicRoot &(oracle a).fst #()), .lam (by is_lc), by is_lc⟩

private def repeatCoin {rT : Type _} (a : Parameters) : Exp rT :=
  .fix (.lam (.cond (.binop .eq (.bvar 0) (.lit (.int 0))) (.lit (.bool true))
    (.cond (.app (root a).fst (.lit .unit))
      (.app (.bvar 1) (.binop .minus (.bvar 0) (.lit (.int 1)))) (.lit (.bool false)))))

theorem bias_power (a : Parameters) (k : ℕ) :
    (IterateCoin.bias (bias a) k : ℝ) = shape a ^ (-(k : ℤ)) := by
  simp [IterateCoin.bias, bias, zpow_neg, zpow_natCast, inv_pow]

private theorem valid_m (a : Parameters) : decide ((a.m : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast Nat.not_le.mpr a.positive)

private theorem valid_ell {rT : Type _} [BEq rT] (a : Parameters) :
    (((BaseLit.int a.ell : BaseLit rT) == .int 1) ||
      ((BaseLit.int a.ell : BaseLit rT) == .int (-1))) = true := by
  rcases a.unit with h | h <;> rw [h] <;> rfl

private theorem valid_minus {rT : Type _} [BEq rT] (a : Parameters) :
    (((BaseLit.int a.ell : BaseLit rT) == .int (-1)) && decide ((a.m : ℤ) < 3)) = false := by
  rcases a.unit with h | h
  · rw [h]
    rfl
  · have hm : ¬(a.m : ℤ) < 3 := by exact_mod_cast Nat.not_lt.mpr (a.minus h)
    rw [h]
    simp [hm]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_oracle (E : CoPset) (a : Parameters) (n den : ℕ)
    (hn : n ≤ den) (hd : 0 < den) :
    ⊢ tglWp E pl(&(oracle a).fst #int (n : ℤ) #int (den : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (AlgebraicRoot.side (bias a) (-1) n den)⌝)) := by
  iterate 2 twp_pure
  simp only [IntegerSign.integerSign_closeRec, IntegerSign.integerSign_openRec]
  iterate 7 twp_pure
  iapply tglWp_wand
  isplitl []
  · iapply IntegerSign.twp_integerSign E _
  iintro %v %hv
  ipureintro
  simpa only [polynomial_sign a n den hn hd] using hv

private theorem twp_root (E : CoPset) (a : Parameters) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a) F) -∗ tglWp E pl(&(root a).fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hroot := AlgebraicRoot.twp_algebraicRoot (rT := rT) (GF := GF) E (bias a)
    (bias_pos a) (bias_lt_one a) (-1) (Or.inr rfl) (oracle a)
    (fun n den hn hd => twp_oracle E a n den hn hd) F
  simp [oracle, Exp.close, Exp.closeRec] at hroot
  iintro Hcredit
  twp_pure
  simp [oracle, Exp.close, Exp.closeRec]
  iapply hroot $$ Hcredit

private theorem root_distSpec (E : CoPset) (a : Parameters) :
    IsDistSpec (GF := GF) E pl(&(root a).fst #()) (RealCoin.law (bias a)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails (twp_root E a F)

private theorem twp_repeatCoin (E : CoPset) (a : Parameters) (k : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (IterateCoin.credit (bias a) k F) -∗ tglWp E pl(&(repeatCoin a) #int (k : ℤ))
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction k generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [IterateCoin.credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ k IH =>
    iintro Hcredit
    iterate 4 twp_pure
    twp_bind pl(&(root a).fst #())
    isimp only [← IterateCoin.expectation (bias a) k F] at Hcredit
    iapply ((root_distSpec E a).wp (IterateCoin.continuation (bias a) k F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [IterateCoin.continuation, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      isimp only [IterateCoin.continuation, ite_true] at Hcredit
      simp [repeatCoin] at IH
      iapply IH $$ Hcredit

/-- The validated wrapper executes the finite product of algebraic-root coins. -/
theorem twp_goldenFamily (E : CoPset) (a : Parameters) (k : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (IterateCoin.credit (bias a) k F) -∗
      tglWp E pl(&Occil.Constants.goldenFamily #int (a.m : ℤ) #int a.ell #int (k : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hrepeat := twp_repeatCoin (rT := rT) (GF := GF) E a k F
  simp [repeatCoin, root, oracle, Exp.close, Exp.closeRec] at hrepeat
  iintro Hcredit
  twp_pures
  rw [valid_m a, Bool.or_false]
  twp_pure
  twp_pures
  rw [valid_ell a]
  twp_pure
  twp_pures
  rw [valid_minus a]
  iterate 3 twp_pure
  simp only [AlgebraicRoot.algebraicRoot_closeRec, AlgebraicRoot.algebraicRoot_openRec,
    IntegerSign.integerSign_closeRec, IntegerSign.integerSign_openRec]
  iapply hrepeat $$ Hcredit

/-- Bernoulli at `G(m,ell)^(-k)`, for every valid parameter and every natural exponent. -/
theorem goldenFamily_distSpec (E : CoPset) (a : Parameters) (k : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.goldenFamily #int (a.m : ℤ) #int a.ell #int (k : ℤ) #())
      (IterateCoin.law (bias a) k) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law, IterateCoin.credit] using
      wand_entails (twp_goldenFamily E a k F)

end specification

end

end SampLib.GoldenFamily
