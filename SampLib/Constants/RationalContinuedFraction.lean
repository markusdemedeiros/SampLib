import SampLib.Constants.Laws.RationalContinuedFraction
import SampLib.Uniform.RationalCoin
import SampLib.Common.WeightedAmplification
import Samplers.Constants.Engines

/-! # Rational generalized continued fractions with uniform coefficient progress

The canonical fraction is determined by its finite prefixes. The recursion may
call both the tail and itself; a bounded state potential pays each call separately.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.RationalContinuedFraction

noncomputable section

/-- The callback representation `(b,(a,last))`. -/
def encodeCoefficient {rT : Type _} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.numerator)
    (Val.pair (Val.int c.denominator) (Val.pair (Val.int c.scale) (Val.bool c.last)))

private theorem valid_guard (c : Coefficient) :
    ((decide ((c.numerator : ℤ) ≤ 0) || decide ((c.denominator : ℤ) < c.numerator)) ||
      decide ((c.scale : ℤ) ≤ 0)) = false := by
  have hab : (c.numerator : ℤ) ≤ c.denominator := by exact_mod_cast c.bounded
  simp [c.positive.ne', c.scale_pos.ne', not_lt.mpr hab]

theorem rationalContinuedFraction_lc {rT : Type _} :
    (Occil.Constants.rationalContinuedFraction : Exp rT).IsLocallyClosed := by is_lc

theorem rationalContinuedFraction_fv {rT : Type _} :
    (Occil.Constants.rationalContinuedFraction : Exp rT).fv = ∅ := by
  simp [Occil.Constants.rationalContinuedFraction, Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem rationalContinuedFraction_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.rationalContinuedFraction =
      Occil.Constants.rationalContinuedFraction :=
  (Exp.open_lc k e _ rationalContinuedFraction_lc).symm

@[simp] theorem rationalContinuedFraction_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.rationalContinuedFraction : Exp rT) =
      Occil.Constants.rationalContinuedFraction :=
  Exp.closeRec_fresh x _ k (by simp [rationalContinuedFraction_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] rationalContinuedFraction_openRec
  rationalContinuedFraction_closeRec RationalCoin.rationalCoin_openRec
  RationalCoin.rationalCoin_closeRec

private theorem direct_distSpec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (c.numerator : ℤ)
      #int (c.denominator : ℤ)) (RealCoin.law (direct c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

private theorem selector_distSpec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (c.denominator : ℤ)
      #int ((c.denominator : ℤ) + c.scale)) (RealCoin.law (selector c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by have := c.denominator_pos; have := c.scale_pos; omega) (by omega)

set_option maxHeartbeats 1200000 in
private theorem twp_weighted (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ∀ i : {i // Reachable a start i}, ↯ (ε * potential (a i.val)) -∗
      ∀ F : Bool → ℝ≥0∞, ↯ (RealCoin.credit (value a i.val) F) -∗
        tglWp E pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (i.val : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply ErrorCredit.Induction.weighted
    (fun i : {i // Reachable a start i} => potential (a i.val))
    (fun i => one_le_potential (a i.val)) _ ε hε (4 / 3) (by norm_num) $$ []
  iintro !> %ε %hε #IH %i Hterm %F Hcredit
  isimp only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] at IH
  iterate 3 twp_pure
  twp_bind pl(&coefficient.fst #int (i.val : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hcoefficient i.val i.property
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard (a i.val)]
  twp_pure
  cases hlast : (a i.val).last
  · iterate 2 twp_pure
    twp_bind pl(&Occil.rationalCoin #int ((a i.val).denominator : ℤ)
      #int ((a i.val).denominator + (a i.val).scale : ℤ))
    icombine Hcredit Hterm as Htotal
    ihave Hsample := ErrorCredit.weaken (expectation a i.val hlast F ε) $$ Htotal
    isimp only [← RealCoin.lintegral_law] at Hsample
    iapply ((selector_distSpec E (a i.val)).wp
      (selectorCredit a i.val F ε) (measurable_of_countable _) _) $$ Hsample
    iintro %selected Hcredit
    cases selected
    · iterate 2 twp_pure
      isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Htail, Hterm⟩ := ErrorCredit.split $$ Hcredit
      let inext : {j // Reachable a start j} :=
        ⟨i.val + 1, reachable_next i.property hlast⟩
      twp_bind pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst
        #int ((i.val : ℤ) + 1))
      rw [← Nat.cast_add_one]
      iapply tglWp_wand
      isplitl [Htail Hterm]
      · iapply IH $$ %inext Hterm %(tailCredit a i.val F ε) Htail
      iintro %v ⟨%b, %hv, Hcredit⟩
      subst v
      cases b
      · twp_pure
        isimp only [tailCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        ieval (
          change _ ⊢ tglWp E
            pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (i.val : ℤ)) _)
        iapply IH $$ %i Hterm %F Hcredit
      · twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [tailCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial
    · twp_pure
      isimp only [selectorCredit, ite_true] at Hcredit
      isimp only [← RealCoin.lintegral_law] at Hcredit
      iapply (direct_distSpec E (a i.val)).spec F (measurable_of_countable _) $$ Hcredit
  · twp_pure
    isimp only [value_last a i.val hlast, ← RealCoin.lintegral_law] at Hcredit
    iapply (direct_distSpec E (a i.val)).spec F (measurable_of_countable _) $$ Hcredit

/-- CTE sampling of the canonical fraction. Only reachable coefficients are queried. -/
theorem twp_rationalContinuedFraction (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (value a start) F) -∗
      tglWp E pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (start : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  have hε : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  ihave Hterm := ErrorCredit.weaken (initial_budget (a start) δ) $$ Hterm
  iapply twp_weighted E a start coefficient hcoefficient (δ / 2) hε $$
    %⟨start, reachable_self a start⟩ Hterm %F Hcredit

/-- Bernoulli at the unique value of all finite continued-fraction prefixes. -/
theorem rationalContinuedFraction_distSpec (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.rationalContinuedFraction &coefficient.fst #int (start : ℤ))
      (RealCoin.law (value a start)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_rationalContinuedFraction E a start coefficient hcoefficient F)

end specification

end

end SampLib.RationalContinuedFraction
