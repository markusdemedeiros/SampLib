import SampLib.Distributions.EpsilonDivision
import Samplers.Bernoulli.Linear

/-! # Derived epsilon-division factory

A successful rational coin exits. Otherwise the verified linear complement coin
chooses between retry and failure. Their three masses normalize to epsilon/p.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.EpsilonDivision

noncomputable section

private def source {rT : Type} : Val rT :=
  ⟨Occil.FactoryExtra.epsilonDivision, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type} :
    (source (rT := rT)).fst = Occil.FactoryExtra.epsilonDivision := rfl

private def loop {rT : Type} (coin : Val rT) (a b lowerNum lowerDen : ℤ) : Val rT :=
  ⟨.fix (.lam (pl% if &Occil.rationalCoin #int a #int b then #true else
    if &Occil.FactoryExtra.linear &(CoinComplement.callback coin).fst
      #int b (#int b - #int a) #int (marginNum a b lowerNum lowerDen)
      #int (marginDen a b lowerDen) #()
    then {Exp.bvar 1} #() else #false)), .fix (by is_lc), by is_lc⟩

private theorem valid_test (a b lowerNum lowerDen : ℤ) (ha : 0 ≤ a) (hab : a < b)
    (hd : 0 < lowerDen) (hl : lowerNum ≤ lowerDen) :
    (((decide (a < 0) || decide (b ≤ a)) || decide (lowerDen ≤ 0)) ||
      decide (lowerDen < lowerNum)) = false := by
  simp [not_lt.mpr ha, not_le.mpr hab, not_le.mpr hd, not_lt.mpr hl]

private theorem zero_valid_test (b lowerNum lowerDen : ℤ) (hb : 0 < b)
    (hd : 0 < lowerDen) (hl : lowerNum ≤ lowerDen) :
    (((false || decide (b ≤ 0)) || decide (lowerDen ≤ 0)) ||
      decide (lowerDen < lowerNum)) = false := by
  simp [not_le.mpr hb, not_le.mpr hd, not_lt.mpr hl]

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem margin_test (a b lowerNum lowerDen : ℤ)
    (h : 0 < marginNum a b lowerNum lowerDen) :
    decide (lowerNum * b - a * lowerDen ≤ 0) = false := decide_eq_false (not_le.mpr h)

private theorem zero_expectation (F : Bool → ℝ≥0∞) :
    (∫⁻ z, F z ∂RealCoin.law 0) = F false := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Zero epsilon returns immediately, even with a negative lower numerator or zero input bias. -/
theorem epsilonDivision_zero_distSpec (E : CoPset) (b lowerNum lowerDen : ℤ)
    (hb : 0 < b) (hd : 0 < lowerDen) (hl : lowerNum ≤ lowerDen) (coin : Val rT) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.epsilonDivision &coin.fst #0 #int b #int lowerNum #int lowerDen #())
      (RealCoin.law 0) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 6 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst, LinearFactorySyntax.linear_openRec,
      LinearFactorySyntax.linear_closeRec, RationalCoin.rationalCoin_openRec,
      RationalCoin.rationalCoin_closeRec])
    twp_pures
    rw [zero_valid_test b lowerNum lowerDen hb hd hl]
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [zero_expectation] at Hcredit
    iframe Hcredit
    itrivial

variable [ProbLangDist.IsUniformInt rT]

/-- A unit lower bound bypasses the callback and returns the rational coin. -/
theorem epsilonDivision_fullLower_distSpec (E : CoPset) (a b lowerDen : ℤ)
    (ha : 0 ≤ a) (hab : a < b) (hd : 0 < lowerDen) (coin : Val rT) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.epsilonDivision &coin.fst #int a #int b
        #int lowerDen #int lowerDen #()) (RealCoin.law (selector a b ha hab)) Val.bool where
  spec F hF := by
    by_cases hz : a = 0
    · subst a
      have h := (epsilonDivision_zero_distSpec (rT := rT) (GF := GF)
        E b lowerDen lowerDen hab hd le_rfl coin).spec F hF
      simpa [selector, RationalCoin.bias, RealCoin.lintegral_law, RealCoin.credit,
        RealCoin.pmf] using h
    have hs := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E a b ha (lt_of_le_of_lt ha hab) hab.le
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 6 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst, LinearFactorySyntax.linear_openRec,
      LinearFactorySyntax.linear_closeRec, RationalCoin.rationalCoin_openRec,
      RationalCoin.rationalCoin_closeRec])
    twp_pures
    rw [valid_test a b lowerDen lowerDen ha hab hd le_rfl]
    twp_pures
    rw [int_beq, beq_eq_false_iff_ne.mpr hz]
    iterate 2 twp_pure
    rw [int_beq, beq_self_eq_true]
    twp_pure
    isimp only [selector] at Hcredit
    iapply hs.spec F hF $$ Hcredit

/-- One iteration uses the rational selector and the linear callback in sequence. -/
private theorem twp_loop (E : CoPset) (p : unitInterval) (a b lowerNum lowerDen : ℤ)
    (h : Admissible p a b lowerNum lowerDen) (ha : 0 < a) (hl : lowerNum < lowerDen)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p a b lowerNum lowerDen h) F) -∗
      tglWp E pl(&(loop coin a b lowerNum lowerDen).fst #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  have hs := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
    E a b h.1 (lt_of_le_of_lt h.1 h.2.1) h.2.1.le
  have hc := CoinComplement.distSpec E p coin hcoin
  have ht := LinearFactory.linear_distSpec E (unitInterval.symm p) b (b - a)
    (marginNum a b lowerNum lowerDen) (marginDen a b lowerDen)
    (linear_admissible p a b lowerNum lowerDen h ha hl) (CoinComplement.callback coin) hc
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (BernoulliRetry.one_lt_factor (unitInterval.symm p)
      (retry_lt_one p a b lowerNum lowerDen h ha)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 (twp_step; simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst,
    LinearFactorySyntax.linear_openRec, RationalCoin.rationalCoin_openRec])
  twp_bind pl(&Occil.rationalCoin #int a #int b)
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation p a b lowerNum lowerDen h ha hl F ε)
    $$ Hcredit
  isimp only [← RealCoin.lintegral_law, selector] at Hcredit
  iapply (hs.wp (selectorCredit p a b lowerNum lowerDen h ha hl F ε)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %z Hcredit
  cases z
  · twp_pure
    twp_pure
    simp only [Exp.ofVal]
    twp_bind pl(&Occil.FactoryExtra.linear &(CoinComplement.callback coin).fst
      #int b #int (b - a) #int (marginNum a b lowerNum lowerDen)
      #int (marginDen a b lowerDen) #())
    isimp only [selectorCredit, Bool.false_eq_true, ite_false,
      ← RealCoin.lintegral_law, innerBias] at Hcredit
    iapply (ht.wp (innerCredit p a b lowerNum lowerDen h F ε)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [innerCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [innerCredit, ite_true, retryCredit] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      iapply IH $$ Hterm Hcredit
  · twp_pure
    twp_value
    imodintro
    iexists true
    isimp only [selectorCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Derived epsilon/p law, including both callback-free early returns. -/
theorem epsilonDivision_distSpec (E : CoPset) (p : unitInterval)
    (a b lowerNum lowerDen : ℤ) (h : Admissible p a b lowerNum lowerDen) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.epsilonDivision &coin.fst #int a #int b
        #int lowerNum #int lowerDen #())
      (RealCoin.law (bias p a b lowerNum lowerDen h)) Val.bool where
  spec F hF := by
    by_cases hz : a = 0
    · subst a
      simpa only [bias_zero] using (epsilonDivision_zero_distSpec (rT := rT) (GF := GF)
        E b lowerNum lowerDen h.2.1 h.2.2.1 h.2.2.2.1 coin).spec F hF
    have ha : 0 < a := lt_of_le_of_ne h.1 (Ne.symm hz)
    by_cases heq : lowerNum = lowerDen
    · subst lowerNum
      rw [bias_full_lower p a b lowerDen h ha]
      iapply (epsilonDivision_fullLower_distSpec E a b lowerDen h.1 h.2.1 h.2.2.1 coin).spec F hF
    have hl : lowerNum < lowerDen := lt_of_le_of_ne h.2.2.2.1 heq
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 6 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst, LinearFactorySyntax.linear_openRec,
      LinearFactorySyntax.linear_closeRec, RationalCoin.rationalCoin_openRec,
      RationalCoin.rationalCoin_closeRec])
    twp_pures
    rw [valid_test a b lowerNum lowerDen h.1 h.2.1 h.2.2.1 h.2.2.2.1]
    twp_pures
    rw [int_beq, beq_eq_false_iff_ne.mpr hz]
    iterate 2 twp_pure
    rw [int_beq, beq_eq_false_iff_ne.mpr heq]
    twp_pures
    rw [margin_test a b lowerNum lowerDen (h.2.2.2.2 hz).1]
    iterate 2 twp_pure
    simp only [LinearFactorySyntax.linear_openRec, RationalCoin.rationalCoin_openRec]
    isimp only [RealCoin.lintegral_law] at Hcredit
    have hloop := twp_loop E p a b lowerNum lowerDen h ha hl coin hcoin F
    simp only [loop, CoinComplement.callback, marginNum, marginDen] at hloop
    iapply hloop $$ Hcredit

end specification

end

end SampLib.EpsilonDivision
