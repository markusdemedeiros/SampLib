import SampLib.Core.Retry
import SampLib.Core.SamplerStep
import SampLib.Bernoulli.Laws.ReciprocalAffine
import SampLib.Uniform.UniformInt
import Samplers.Bernoulli.Rational
import Metrology.Iris.LocalBI

/-! # Reciprocal affine factory

A uniform rank selects a successful exit, an unsuccessful exit, or an input-coin
trial. The three interval widths identify the normalized reciprocal affine law.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ReciprocalAffine

noncomputable section

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
  iapply Retry.twp_loop solve_not_value
    (BernoulliRetry.one_lt_factor (retry p (a * y) (b * y) hc)
      (retry_lt_one p (a * y) (b * y) hc))
  iintro !> %ε %hε IH Hcredit
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
        twp_bind pl(&(source (rT := rT)).fst &coin.fst
          #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hcredit
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
