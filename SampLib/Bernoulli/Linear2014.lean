import SampLib.Bernoulli.Support.Linear2014Loop

/-! # Huber's geometric-jump linear factory -/

open ProbLang
open scoped ENNReal SampLib.Linear2014.Syntax SampLib.LinearPowerWalk.Syntax

namespace SampLib.Linear2014

noncomputable section

private theorem valid_test (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    Bool.or (decide (a < 0)) (decide (b ≤ 0)) = false := by
  simp [not_lt.mpr ha, not_le.mpr hb]

private theorem margin_test (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (hba : b < a) :
    Bool.or (decide (e ≤ 0)) (decide (f ≤ e)) = false := by
  obtain ⟨he, hef, _⟩ := h.2.2 hba
  simp [not_le.mpr he, not_le.mpr hef]

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

private theorem twp_open (E : CoPset) (coin : Val rT) (a b e f : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (Syntax.body coin a b e f) Φ ⊢
      tglWp E pl(&Occil.FactoryExtra.linear2014 &coin.fst
        #int a #int b #int e #int f #()) Φ := by
  have hc : Exp.lcb (Syntax.arguments coin a b e f).length
      (Syntax.sourceBody : Exp rT) = true := Syntax.sourceBody_lcb
  have h := CurriedStep.twp_apply E [] (Syntax.arguments coin a b e f) Syntax.sourceBody hc Φ
  rw [Syntax.opened_source] at h
  simpa only [Syntax.arguments, List.length_cons, List.length_nil, Nat.reduceAdd,
    ← Syntax.source_eq, CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, EctxItem.fillItem, Exp.ofVal, flip] using h

private theorem twp_initial_call (E : CoPset) (coin : Val rT) (a b e f : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(Syntax.loop coin).fst #1 #int a #int b #int e #int f
      (#23 * #int f) (#5 * #int e)) Φ ⊢
    tglWp E (.app (.lam pl({Exp.bvar 0} #1 #int a #int b #int e #int f
      (#23 * #int f) (#5 * #int e))) (Syntax.loop coin).fst) Φ := by
  have h := twp_beta E [] pl({Exp.bvar 0} #1 #int a #int b #int e #int f
    (#23 * #int f) (#5 * #int e)) (Syntax.loop coin) (by is_lc) Φ
  simpa only [Ectx.fill, List.foldl_nil, Exp.open', Exp.openRec, ProbLang.openRec_val_fst, ite_true]
    using h

variable [ProbLangDist.IsUniformInt rT]

private theorem contracting_spec (E : CoPset) (p : unitInterval)
    (σ : LinearFactory.Parameters p) (hab : σ.a ≤ σ.b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(if &Occil.rationalCoin #int σ.a #int σ.b then &coin.fst #() else #false)
      (RealCoin.law σ.bias) Val.bool where
  spec F _ := by
    iintro Hcredit
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

private theorem expanding_spec (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&(Syntax.loop coin).fst #1 #int σ.a #int σ.b #int σ.e #int σ.f
        #int σ.numerator #int σ.denominator) (RealCoin.law σ.bias) Val.bool where
  spec F _ := by
    have hp := twp_loop E p σ 1 (by norm_num) coin hcoin F
    simpa only [IterateCoin.credit, IterateCoin.bias, pow_one, Nat.cast_one,
      RealCoin.lintegral_law] using
      wand_entails hp

/-- Both coefficient branches and both source margin choices satisfy the linear law. -/
theorem twp_linear2014 (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂RealCoin.law (LinearFactory.bias p a b e f h)) -∗
      tglWp E pl(&Occil.FactoryExtra.linear2014 &coin.fst
        #int a #int b #int e #int f #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_open E coin a b e f
  unfold Syntax.body
  twp_pures
  rw [valid_test a b h.1 h.2.1]
  twp_pure
  twp_pure
  by_cases hab : a ≤ b
  · rw [decide_eq_true hab]
    twp_pure
    have hs : IsDistSpec (GF := GF) E
        pl(if &Occil.rationalCoin #int a #int b then &coin.fst #() else #false)
        (RealCoin.law (LinearFactory.bias p a b e f h)) Val.bool :=
      contracting_spec E p ⟨a, b, e, f, h⟩ hab coin hcoin
    iapply hs.spec F (measurable_of_countable _) $$ Hcredit
  · have hba : b < a := lt_of_not_ge hab
    have hloop := expanding_spec E p (Parameters.initial p a b e f h hba) coin hcoin
    rw [Parameters.initial_bias] at hloop
    rw [decide_eq_false hab]
    twp_pure
    twp_pures
    rw [margin_test p a b e f h hba]
    twp_pure
    iterate 3 twp_pure
    by_cases hc : 1000 * e ≤ 644 * f
    · rw [decide_eq_true hc]
      twp_pure
      iterate 5 twp_pure
      iapply twp_initial_call E coin a b e f
      iterate 2 twp_pure
      simp only [Exp.ofVal]
      have hs := hloop
      simp only [Parameters.initial, dite_eq_left hc] at hs
      iapply hs.spec F (measurable_of_countable _) $$ Hcredit
    · rw [decide_eq_false hc]
      twp_pure
      iterate 5 twp_pure
      iapply twp_initial_call E coin a b 644 1000
      iterate 2 twp_pure
      simp only [Exp.ofVal]
      have hs := hloop
      simp only [Parameters.initial, dite_eq_right hc] at hs
      iapply hs.spec F (measurable_of_countable _) $$ Hcredit

/-- Huber's geometric-jump factory samples Bernoulli(`(a/b)*p`) on its full source domain. -/
theorem linear2014_distSpec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linear2014 &coin.fst #int a #int b #int e #int f #())
      (RealCoin.law (LinearFactory.bias p a b e f h)) Val.bool where
  spec F _ := wand_entails (twp_linear2014 E p a b e f h coin hcoin F)

end specification

end

end SampLib.Linear2014
