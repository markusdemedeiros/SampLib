import SampLib.Constants.Laws.GeneralizedContinuedFraction
import SampLib.Uniform.RationalCoin
import SampLib.Common.WeightedAmplification
import Samplers.Constants.Engines

/-! # Positive integer generalized continued fractions

The canonical fraction is determined by its finite prefixes. The recursion may
call both the tail and itself; a bounded state potential pays each call separately.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.ContinuedFraction

noncomputable section

/-- The callback representation `(b,(a,last))`. -/
def encodeCoefficient {rT : Type _} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.numerator) (Val.pair (Val.int c.denominator) (Val.bool c.last))

private theorem valid_guard (b a : ℕ) (hb : 0 < b) (hba : b ≤ a) :
    (decide ((b : ℤ) ≤ 0) || decide ((a : ℤ) < b)) = false := by
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem generalizedContinuedFraction_lc {rT : Type _} :
    (Occil.Constants.generalizedContinuedFraction : Exp rT).IsLocallyClosed := by is_lc

theorem generalizedContinuedFraction_fv {rT : Type _} :
    (Occil.Constants.generalizedContinuedFraction : Exp rT).fv = ∅ := by
  simp [Occil.Constants.generalizedContinuedFraction, Exp.fv, RationalCoin.rationalCoin_fv]

@[simp] theorem generalizedContinuedFraction_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.generalizedContinuedFraction =
      Occil.Constants.generalizedContinuedFraction :=
  (Exp.open_lc k e _ generalizedContinuedFraction_lc).symm

@[simp] theorem generalizedContinuedFraction_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.generalizedContinuedFraction : Exp rT) =
      Occil.Constants.generalizedContinuedFraction :=
  Exp.closeRec_fresh x _ k (by simp [generalizedContinuedFraction_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem direct_distSpec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (c.numerator : ℤ)
      #int (c.denominator : ℤ)) (RealCoin.law (direct c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by exact_mod_cast c.denominator_pos) (by exact_mod_cast c.bounded)

private theorem selector_distSpec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (c.denominator : ℤ)
      #int ((c.denominator : ℤ) + 1)) (RealCoin.law (selector c)) Val.bool :=
  RationalCoin.rationalCoin_distSpec E _ _ (by positivity)
    (by have := c.denominator_pos; omega) (by omega)

/-- One round of the source after it reads and checks the coefficient `(b,(a,last))`. -/
def round {rT : Type _} (coefficient : Val rT) (i : ℕ) (b a : ℕ) (last : Bool) : Exp rT :=
  if last then pl(&Occil.rationalCoin #int (b : ℤ) #int (a : ℤ))
  else pl(if &Occil.rationalCoin #int (a : ℤ) #int ((a : ℤ) + 1)
    then &Occil.rationalCoin #int (b : ℤ) #int (a : ℤ)
    else if &Occil.Constants.generalizedContinuedFraction &coefficient.fst (#int (i : ℤ) + #1)
      then #false
      else &Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (i : ℤ))

set_option maxHeartbeats 600000 in
omit [ProbLangDist.IsUniformInt rT] in
/-- Reading and checking a valid coefficient leaves one round of the source. -/
theorem twp_entry (E : CoPset) (coefficient : Val rT) (i b a : ℕ) (last : Bool)
    (hb : 0 < b) (hba : b ≤ a)
    (hentry : ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ)) (fun v : Val rT =>
      iprop(⌜v = Val.pair (Val.int b) (Val.pair (Val.int a) (Val.bool last))⌝)))
    (Φ : Val rT → IProp GF) :
    tglWp E (round coefficient i b a last) Φ ⊢
      tglWp E pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (i : ℤ))
        Φ := by
  iintro Hround
  iterate 3 twp_pure
  twp_bind pl(&coefficient.fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hentry
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard b a hb hba]
  twp_pure
  simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
  cases last
  · iterate 2 twp_pure
    ieval (change _ ⊢ tglWp E (round coefficient i b a false) Φ)
    iexact Hround
  · twp_pure
    ieval (change _ ⊢ tglWp E (round coefficient i b a true) Φ)
    iexact Hround

private theorem twp_weighted (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ∀ i : {i // Reachable a start i}, ↯ (ε * potential (a i.val)) -∗
      ∀ F : Bool → ℝ≥0∞, ↯ (RealCoin.credit (value a i.val) F) -∗
        tglWp E pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (i.val : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply ErrorCredit.Induction.weighted
    (fun i : {i // Reachable a start i} => potential (a i.val))
    (fun i => one_le_potential (a i.val)) _ ε hε (4 / 3) (by norm_num) $$ []
  iintro !> %ε %hε #IH %i Hterm %F Hcredit
  isimp only [ENNReal.coe_div (by norm_num : (3 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] at IH
  iapply twp_entry E coefficient i.val (a i.val).numerator (a i.val).denominator
    (a i.val).last (a i.val).positive (a i.val).bounded (hcoefficient i.val i.property)
  cases hlast : (a i.val).last
  · simp only [round, Bool.false_eq_true, ite_false]
    twp_bind pl(&Occil.rationalCoin #int ((a i.val).denominator : ℤ)
      #int ((a i.val).denominator + 1 : ℤ))
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
      twp_bind pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst
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
            pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (i.val : ℤ)) _)
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
  · simp only [round, ite_true]
    isimp only [value_last a i.val hlast, ← RealCoin.lintegral_law] at Hcredit
    iapply (direct_distSpec E (a i.val)).spec F (measurable_of_countable _) $$ Hcredit

/-- CTE sampling of the canonical fraction. Only reachable coefficients are queried. -/
theorem twp_generalizedContinuedFraction (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (value a start) F) -∗
      tglWp E pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (start : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  have hε : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  ihave Hterm := ErrorCredit.weaken (initial_budget (a start) δ) $$ Hterm
  iapply twp_weighted E a start coefficient hcoefficient (δ / 2) hε $$
    %⟨start, reachable_self a start⟩ Hterm %F Hcredit

/-- Bernoulli at the unique value of all finite continued-fraction prefixes. -/
theorem generalizedContinuedFraction_distSpec (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (hcoefficient : ∀ i, Reachable a start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.generalizedContinuedFraction &coefficient.fst #int (start : ℤ))
      (RealCoin.law (value a start)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_generalizedContinuedFraction E a start coefficient hcoefficient F)

end specification

end

end SampLib.ContinuedFraction
