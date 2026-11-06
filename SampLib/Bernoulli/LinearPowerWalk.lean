import SampLib.Bernoulli.Support.LinearPowerWalkLoop

/-! # Huber's joint linear-and-power factory -/

open ProbLang
open scoped ENNReal SampLib.LinearPowerWalk.Syntax

namespace SampLib.LinearPowerWalk

noncomputable section

private theorem valid_test (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    Bool.or (Bool.or (decide (a < 0)) (decide (b ≤ 0))) false = false := by
  simp [not_lt.mpr ha, not_le.mpr hb]

private theorem margin_test (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) :
    Bool.or (decide (e ≤ 0)) (decide (f ≤ e)) = false := by
  obtain ⟨he, hef, _⟩ := h.2.2 hba
  simp [not_le.mpr he, not_le.mpr hef]

private theorem opened_loop_call {rT : Type} (coin : Val rT) (a b n e f : ℤ) :
    Exp.open' pl({Exp.bvar 0} #int n #int a #int b #int e #int f) (Syntax.loop coin).fst =
      pl(&(Syntax.loop coin).fst #int n #int a #int b #int e #int f) := rfl

private theorem contracting_expectation {p : unitInterval} (σ : LinearFactory.Parameters p)
    (hab : σ.a ≤ σ.b) (F : Bool → ℝ≥0∞) :
    (∫⁻ z, LinearFactory.contractingCredit p F z ∂RealCoin.law
      (RationalCoin.bias σ.a σ.b σ.admissible.1 σ.admissible.2.1 hab)) =
      ∫⁻ z, F z ∂RealCoin.law σ.bias := by
  simpa only [RealCoin.lintegral_law] using LinearFactory.contracting_expectation σ hab F

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ProbLang.openRec_val_fst

private theorem twp_open (E : CoPset) (coin : Val rT) (a b n e f : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (Syntax.body coin a b n e f) Φ ⊢
      tglWp E pl(&Occil.FactoryExtra.linearPowerWalk &coin.fst
        #int a #int b #int n #int e #int f #()) Φ := by
  have hc : Exp.lcb (Syntax.arguments coin a b n e f).length
      (Syntax.sourceBody : Exp rT) = true := Syntax.sourceBody_lcb
  have h := CurriedStep.twp_apply E [] (Syntax.arguments coin a b n e f) Syntax.sourceBody hc Φ
  rw [Syntax.opened_source] at h
  simpa only [Syntax.arguments, List.length_cons, List.length_nil, Nat.reduceAdd,
    ← Syntax.source_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, EctxItem.fillItem, Exp.ofVal, flip] using h

private theorem twp_loop_call (E : CoPset) (coin : Val rT) (a b n e f : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(Syntax.loop coin).fst #int n #int a #int b #int e #int f) Φ ⊢
      tglWp E (.app (.lam pl({Exp.bvar 0} #int n #int a #int b #int e #int f))
        (Syntax.loop coin).fst) Φ := by
  have h := twp_beta E [] pl({Exp.bvar 0} #int n #int a #int b #int e #int f)
    (Syntax.loop coin) (by is_lc) Φ
  simpa only [Ectx.fill, List.foldl_nil, opened_loop_call] using h

variable [ProbLangDist.IsUniformInt rT]

private theorem contracting_spec (E : CoPset) (p : unitInterval)
    (σ : LinearFactory.Parameters p) (hab : σ.a ≤ σ.b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(Syntax.contracting coin σ.a σ.b).fst #())
      (RealCoin.law σ.bias) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&Occil.rationalCoin #int σ.a #int σ.b)
    isimp only [← contracting_expectation σ hab F] at Hcredit
    iapply ((RationalCoin.rationalCoin_distSpec E σ.a σ.b σ.admissible.1
      σ.admissible.2.1 hab).wp (LinearFactory.contractingCredit p F)
        (measurable_of_countable _) _) $$ Hcredit
    iintro %z Hcredit
    cases z
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [LinearFactory.contractingCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [LinearFactory.contractingCredit, ite_true] at Hcredit
      iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit

private theorem contracting_power_spec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hab : a ≤ b) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.iterateCoin &(Syntax.contracting coin a b).fst #int (n : ℤ))
      (IterateCoin.law (LinearFactory.bias p a b e f h) n) Val.bool :=
  IterateCoin.iterateCoin_distSpec E (LinearFactory.bias p a b e f h)
    (Syntax.contracting coin a b) (contracting_spec E p ⟨a, b, e, f, h⟩ hab coin hcoin) n

private theorem expanding_spec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&(Syntax.loop coin).fst #int (n : ℤ) #int a #int b #int e #int f)
      (IterateCoin.law (LinearFactory.bias p a b e f h) n) Val.bool where
  spec F _ := by
    have hp := twp_loop E p (Parameters.ofAdmissible p a b e f h hba) n coin hcoin F
    rw [Parameters.ofAdmissible_bias] at hp
    simpa only [Parameters.ofAdmissible, IterateCoin.law, RealCoin.lintegral_law,
      IterateCoin.credit] using wand_entails hp

/-- Symbolic execution over the complete conditional-margin parameter domain. -/
theorem twp_linearPowerWalk (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂IterateCoin.law (LinearFactory.bias p a b e f h) n) -∗
      tglWp E pl(&Occil.FactoryExtra.linearPowerWalk &coin.fst
        #int a #int b #int (n : ℤ) #int e #int f #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_open E coin a b (n : ℤ) e f
  unfold Syntax.body
  twp_pures
  rw [valid_test a b h.1 h.2.1]
  twp_pure
  twp_pure
  by_cases hab : a ≤ b
  · rw [decide_eq_true hab]
    twp_pure
    iapply (contracting_power_spec E p a b e f h hab n coin hcoin).spec F
      (measurable_of_countable _) $$ Hcredit
  · have hba : b < a := lt_of_not_ge hab
    rw [decide_eq_false hab]
    twp_pure
    twp_pures
    rw [margin_test p a b e f h hba]
    twp_pure
    iapply twp_loop_call E coin a b (n : ℤ) e f
    iapply (expanding_spec E p a b e f h hba n coin hcoin).spec F
      (measurable_of_countable _) $$ Hcredit

/-- The adaptive joint factory returns Bernoulli(`((a/b)*p)^n`), including zero powers. -/
theorem linearPowerWalk_distSpec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (n : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linearPowerWalk &coin.fst
        #int a #int b #int (n : ℤ) #int e #int f #())
      (IterateCoin.law (LinearFactory.bias p a b e f h) n) Val.bool where
  spec F _ := wand_entails (twp_linearPowerWalk E p a b e f h n coin hcoin F)

end specification

end

end SampLib.LinearPowerWalk
