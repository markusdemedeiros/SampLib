import SampLib.Constants.AlgebraicRoot
import Samplers.Constants.Algebraic

/-! # Deterministic integer signs used by algebraic-root coins -/

open ProbLang

namespace SampLib.IntegerSign

noncomputable section

/-- A positive cofactor preserves the sign on either side of the root. -/
theorem sign_of_left_factor (p : unitInterval) (n den : ℕ) (z : ℤ)
    (a : ℝ) (ha : 0 < a) (hz : (z : ℝ) = ((p : ℝ) * den - n) * a) :
    z.sign = AlgebraicRoot.side p 1 n den := by
  by_cases hl : (n : ℝ) < (p : ℝ) * den
  · have hzpos : (0 : ℝ) < z := by rw [hz]; exact mul_pos (sub_pos.mpr hl) ha
    have hz' : 0 < z := by exact_mod_cast hzpos
    simp [AlgebraicRoot.side, hl, Int.sign_eq_one_of_pos hz']
  · by_cases hr : (p : ℝ) * den < n
    · have hzneg : (z : ℝ) < 0 := by rw [hz]; exact mul_neg_of_neg_of_pos (sub_neg.mpr hr) ha
      have hz' : z < 0 := by exact_mod_cast hzneg
      simp [AlgebraicRoot.side, hl, hr, Int.sign_eq_neg_one_of_neg hz']
    · have he : (p : ℝ) * den - n = 0 := by linarith
      have hz0 : z = 0 := by exact_mod_cast (by simpa [he] using hz : (z : ℝ) = 0)
      simp [AlgebraicRoot.side, hl, hr, hz0]

/-- The opposite orientation follows by negating the polynomial. -/
theorem sign_of_right_factor (p : unitInterval) (n den : ℕ) (z : ℤ)
    (a : ℝ) (ha : 0 < a) (hz : (z : ℝ) = ((n : ℝ) - (p : ℝ) * den) * a) :
    z.sign = AlgebraicRoot.side p (-1) n den := by
  have he : ((-z : ℤ) : ℝ) = ((p : ℝ) * den - n) * a := by
    rw [Int.cast_neg, hz]
    ring
  have h := sign_of_left_factor p n den (-z) a ha he
  rw [Int.sign_neg] at h
  calc
    z.sign = -AlgebraicRoot.side p 1 n den := by
      simpa only [neg_neg] using congrArg Neg.neg h
    _ = AlgebraicRoot.side p (-1) n den := by
      simp only [AlgebraicRoot.side]
      split_ifs <;> rfl

theorem integerSign_lc {rT : Type _} :
    (Occil.Constants.integerSign : Exp rT).IsLocallyClosed := by is_lc

theorem integerSign_fv {rT : Type _} :
    (Occil.Constants.integerSign : Exp rT).fv = ∅ := by
  simp [Occil.Constants.integerSign, Exp.fv]

@[simp] theorem integerSign_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.integerSign = Occil.Constants.integerSign :=
  (Exp.open_lc k e _ integerSign_lc).symm

@[simp] theorem integerSign_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.integerSign : Exp rT) = Occil.Constants.integerSign :=
  Exp.closeRec_fresh x _ k (by simp [integerSign_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The object-language sign is the mathematical integer sign. -/
theorem twp_integerSign (E : CoPset) (n : ℤ) :
    ⊢ tglWp E pl(&Occil.Constants.integerSign #int n)
      (fun v : Val rT => iprop(⌜v = Val.int n.sign⌝)) := by
  twp_pures
  by_cases hneg : n < 0
  · rw [decide_eq_true hneg]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rw [Int.sign_eq_neg_one_of_neg hneg]
  · rw [decide_eq_false hneg]
    twp_pures
    by_cases hz : n = 0
    · subst n
      twp_pures
      twp_value
      imodintro
      itrivial
    · rw [show ((BaseLit.int n : BaseLit rT) == .int 0) = false from by
        change (n == 0) = false
        exact beq_eq_false_iff_ne.mpr hz]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rw [Int.sign_eq_one_of_pos (lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm hz))]

end specification

end

end SampLib.IntegerSign
