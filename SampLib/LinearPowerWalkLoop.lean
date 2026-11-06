import SampLib.Distributions.LinearPowerWalk
import SampLib.Syntax.LinearPowerWalk

/-! # CTE verification of the adaptive power walk

One logistic step preserves the current power. A successful probability
amplification preserves it too, and the work budget pays for total recursion.
-/

open ProbLang
open scoped ENNReal NNReal SampLib.LinearPowerWalk.Syntax

namespace SampLib.LinearPowerWalk

noncomputable section

private def selectorCallback {rT : Type} {p : unitInterval} (σ : Parameters p) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin #int σ.factorDen #int σ.factorNum),
    .lam (by is_lc), by is_lc⟩

private theorem natural_zero_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = decide (n = 0) := by
  change decide ((n : ℤ) = 0) = decide (n = 0)
  exact decide_eq_decide.mpr (by omega)

private theorem int_pred (n : ℕ) (hn : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

private theorem two_coe : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num

private theorem next_call {rT : Type} {p : unitInterval} (loop : Val rT)
    (σ : Parameters p) (n : ℤ) :
    pl(&loop.fst #int n #int (σ.a * (2 * σ.f - σ.e)) #int (σ.b * (2 * (σ.f - σ.e)))
      #int σ.e #int (2 * σ.f)) =
    pl(&loop.fst #int n #int σ.next.a #int σ.next.b #int σ.next.e #int σ.next.f) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ProbLang.openRec_val_fst

private theorem twp_loop_open (E : CoPset) (coin : Val rT) (n a b e f : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (Syntax.step coin n a b e f).val Φ ⊢
      tglWp E pl(&(Syntax.loop coin).fst #int n #int a #int b #int e #int f) Φ := by
  rw [← Syntax.opened_step]
  have hc : Exp.lcb 6 (Exp.openRec 6 coin.fst Syntax.code) = true :=
    Exp.lcb_openRec (Exp.lcb_ofVal 6 coin) Syntax.code_lcb
  simpa only [Syntax.stepBody, Syntax.loop, CurriedStep.application, CurriedStep.context,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil,
    EctxItem.fillItem, Exp.ofVal, flip] using
    CurriedStep.twp_fix_apply E [] (Val.int n) [Val.int a, .int b, .int e, .int f]
      (Exp.openRec 6 coin.fst Syntax.code) hc Φ

variable [ProbLangDist.IsUniformInt rT]

private theorem selectorCallback_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) :
    IsDistSpec (GF := GF) E pl(&(selectorCallback σ).fst #())
      (RealCoin.law σ.selectorBase) Val.bool where
  spec F hF := by
    have h : IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int σ.factorDen #int σ.factorNum)
        (RealCoin.law σ.selectorBase) Val.bool :=
      RationalCoin.rationalCoin_distSpec E σ.factorDen σ.factorNum
        σ.factorDen_pos.le σ.factorNum_pos σ.factor_le
    iintro Hcredit
    twp_pure
    iapply h.spec F hF $$ Hcredit

private theorem power_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.rationalPower &(selectorCallback σ).fst #int (n : ℤ) #1 #())
      (RealCoin.law (σ.selector n)) Val.bool := by
  simpa only [Nat.mul_one, Nat.cast_one, Parameters.selector, IterateCoin.law] using
    RationalPowerInteger.rationalPower_integer_distSpec E σ.selectorBase (selectorCallback σ)
      (selectorCallback_spec E p σ) n 1 (by norm_num)

private theorem logistic_spec (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.logisticFactory &coin.fst #int σ.a #int σ.b #())
      (RealCoin.law (FiniteGeometricWalk.down σ.bias σ.bias.2.1)) Val.bool := by
  simpa only [Gambler.logistic_bias, Parameters.bias_coe] using
    LogisticFactory.logisticFactory_distSpec
    E p σ.a σ.b σ.a_pos σ.b_pos coin hcoin

private theorem twp_loop_positive (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ⊢ ↯ δ -∗ ∀ σ : Parameters p, ∀ n : ℕ, ∀ F : Bool → ℝ≥0∞,
      ↯ (σ.credit n F δ) -∗
      tglWp E pl(&(Syntax.loop coin).fst #int (n : ℤ)
        #int σ.a #int σ.b #int σ.e #int σ.f)
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple hδ (by norm_num : (1 : ℝ≥0) < 2) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %σ %n %F Hcredit
  isimp only [two_coe] at IH
  iapply twp_loop_open E coin (n : ℤ) σ.a σ.b σ.e σ.f
  twp_pure
  rw [natural_zero_test]
  by_cases hn : n = 0
  · subst n
    rw [decide_eq_true rfl]
    twp_pure
    twp_value
    imodintro
    iexists true
    isimp only [σ.credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [decide_eq_false hn]
    twp_pure
    iterate 4 twp_pure
    by_cases hlarge : 355 * σ.f < 100 * (n : ℤ) * σ.e
    · rw [decide_eq_true hlarge]
      twp_pure
      iterate 6 twp_pure
      twp_bind pl(&Occil.FactoryExtra.rationalPower &(selectorCallback σ).fst
        #int (n : ℤ) #1 #())
      icombine Hcredit Hterm as Hcredit
      ihave Hcredit := ErrorCredit.weaken
        (σ.expectation true n hnpos ((σ.threshold_iff n).mp hlarge) F δ) $$ Hcredit
      isimp only [AdaptivePowerWalk.drawBias, ite_true] at Hcredit
      iapply ((power_spec E p σ n).wp
        (AdaptivePowerWalk.stepCredit true σ.margin σ.bias σ.next.bias n F δ)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_value
        imodintro
        iexists false
        isimp only [AdaptivePowerWalk.stepCredit, ite_true, Bool.false_eq_true, ite_false]
          at Hcredit
        iframe Hcredit
        itrivial
      · twp_pure
        iterate 3 twp_pure
        simp only [Exp.ofVal]
        rw [next_call (Syntax.loop coin) σ (n : ℤ)]
        isimp only [AdaptivePowerWalk.stepCredit, ite_true, ← σ.next_margin,
          ← Parameters.credit_eq] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        iapply IH $$ Hterm %σ.next %n %F Hcredit
    · rw [decide_eq_false hlarge]
      twp_pure
      twp_bind pl(&Occil.logisticFactory &coin.fst #int σ.a #int σ.b #())
      icombine Hcredit Hterm as Hcredit
      ihave Hcredit := ErrorCredit.weaken
        (σ.expectation false n hnpos (not_lt.mp (fun h => hlarge ((σ.threshold_iff n).mpr h)))
          F δ) $$ Hcredit
      isimp only [AdaptivePowerWalk.drawBias, Bool.false_eq_true, ite_false] at Hcredit
      iapply ((logistic_spec E p σ coin hcoin).wp
        (AdaptivePowerWalk.stepCredit false σ.margin σ.bias σ.next.bias n F δ)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %z Hcredit
      cases z
      · iterate 3 twp_pure
        rw [← Nat.cast_add_one]
        isimp only [AdaptivePowerWalk.stepCredit, Bool.false_eq_true, ite_false,
          ← Parameters.credit_eq] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        iapply IH $$ Hterm %σ %(n + 1) %F Hcredit
      · iterate 3 twp_pure
        rw [int_pred n hnpos]
        isimp only [AdaptivePowerWalk.stepCredit, Bool.false_eq_true, ite_false, ite_true,
          ← Parameters.credit_eq]
          at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        iapply IH $$ Hterm %σ %(n - 1) %F Hcredit

/-- The adaptive loop has its full power law for every initial exponent and valid margin. -/
theorem twp_loop (E : CoPset) (p : unitInterval) (σ : Parameters p) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (IterateCoin.credit σ.bias n F) -∗
      tglWp E pl(&(Syntax.loop coin).fst #int (n : ℤ)
        #int σ.a #int σ.b #int σ.e #int σ.f)
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  let δ := σ.initialSlack n ε
  have hδ : 0 < δ := σ.initialSlack_pos n ε hε
  ihave Hterm := ErrorCredit.weaken (le_of_eq (σ.initialSlack_budget n ε)) $$ Hterm
  ihave ⟨Hwork, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hwork as Hcredit
  isimp only [← Parameters.credit_eq] at Hcredit
  iapply (twp_loop_positive E p coin hcoin δ hδ) $$ Hterm %σ %n %F Hcredit

end specification

end

end SampLib.LinearPowerWalk
