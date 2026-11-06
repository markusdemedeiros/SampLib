import SampLib.Bernoulli.Laws.Linear2014Credit
import SampLib.Bernoulli.Syntax.Linear2014

/-! # CTE execution of Huber's geometric-jump factory -/

open ProbLang
open scoped ENNReal NNReal SampLib.Linear2014.Syntax SampLib.LinearPowerWalk.Syntax

namespace SampLib.Linear2014

noncomputable section

private def jumpCallback {rT : Type} {p : unitInterval} (σ : Parameters p) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin (#int σ.a - #int σ.b) #int σ.a),
    .lam (by is_lc), by is_lc⟩

private def drawNext {rT : Type} {p : unitInterval} (coin : Val rT)
    (σ : Parameters p) (s : ℕ) : Exp rT :=
  pl(if &coin.fst #() then #int ((s : ℤ) - 1) else
    #int ((s : ℤ) - 1) + #1 + &Occil.geometric &(jumpCallback σ).fst #())

private theorem natural_zero_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = decide (n = 0) := by
  change decide ((n : ℤ) = 0) = decide (n = 0)
  exact decide_eq_decide.mpr (by omega)

private theorem next_call {rT : Type} {p : unitInterval} (loop : Val rT)
    (σ : Parameters p) (n : ℤ) :
    pl(&loop.fst #int n #int (σ.a * (2 * σ.f + σ.e)) #int (σ.b * (2 * σ.f))
      #int σ.e #int (2 * σ.f) #int (2 * σ.numerator) #int σ.denominator) =
    pl(&loop.fst #int n #int σ.next.a #int σ.next.b #int σ.next.e #int σ.next.f
      #int σ.next.numerator #int σ.next.denominator) := rfl

private theorem two_coe : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num

private theorem int_pred (n : ℕ) (hn : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

private def selectorCallback {rT : Type} {p : unitInterval} (σ : Parameters p) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin #int σ.factorDen #int σ.factorNum),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ProbLang.openRec_val_fst

private theorem twp_loop_open (E : CoPset) (coin : Val rT) (n a b e f N D : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (Syntax.step coin n a b e f N D).val Φ ⊢
      tglWp E pl(&(Syntax.loop coin).fst
        #int n #int a #int b #int e #int f #int N #int D) Φ := by
  rw [← Syntax.opened_step]
  have hc : Exp.lcb 8 (Exp.openRec 8 coin.fst Syntax.code) = true :=
    Exp.lcb_openRec (Exp.lcb_ofVal 8 coin) Syntax.code_lcb
  simpa only [Syntax.stepBody, Syntax.loop, CurriedStep.application, CurriedStep.context,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, EctxItem.fillItem, Exp.ofVal, flip] using
    CurriedStep.twp_fix_apply E [] (Val.int n)
      [Val.int a, .int b, .int e, .int f, .int N, .int D]
      (Exp.openRec 8 coin.fst Syntax.code) hc Φ

variable [ProbLangDist.IsUniformInt rT]

private theorem jumpCallback_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) :
    IsDistSpec (GF := GF) E pl(&(jumpCallback σ).fst #())
      (RealCoin.law σ.jumpBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_pure
    simp only [Exp.ofVal]
    isimp only [Parameters.jumpBias] at Hcredit
    iapply (RationalCoin.rationalCoin_distSpec E (σ.a - σ.b) σ.a
      (sub_pos.mpr σ.b_lt_a).le σ.a_pos (sub_le_self _ σ.b_pos.le)).spec F hF $$ Hcredit

private theorem jump_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) :
    IsDistSpec (GF := GF) E pl(&Occil.geometric &(jumpCallback σ).fst #())
      (Geometric.law σ.jumpBias) (fun n : ℕ => Val.int (n : ℤ)) :=
  Geometric.geometric_distSpec E σ.jumpBias σ.jumpBias_pos (jumpCallback σ)
    (jumpCallback_spec E p σ)

private theorem drawNext_spec (E : CoPset) (p : unitInterval) (σ : Parameters p)
    (coin : Val rT) (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #())
      (RealCoin.law p) Val.bool) (s : ℕ) (hs : 0 < s) :
    IsDistSpec (GF := GF) E (drawNext coin σ s) (Linear2014Jump.law p σ.jumpBias s)
      (fun n : ℕ => Val.int (n : ℤ)) where
  spec H _ := by
    iintro Hcredit
    unfold drawNext
    twp_bind pl(&coin.fst #())
    isimp only [Linear2014Jump.lintegral_law] at Hcredit
    iapply (hcoin.wp (fun z => if z then H (s - 1) else
      ∫⁻ n, H (s + n) ∂Geometric.law σ.jumpBias) (measurable_of_countable _) _) $$ Hcredit
    iintro %z Hcredit
    cases z
    · twp_pure
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      twp_bind pl(&Occil.geometric &(jumpCallback σ).fst #())
      iapply ((jump_spec E p σ).wp (fun n => H (s + n))
        (measurable_of_countable _) _) $$ Hcredit
      iintro %n Hcredit
      twp_pures
      rw [show (s : ℤ) - 1 + 1 + n = ((s + n : ℕ) : ℤ) by push_cast; omega]
      twp_value
      imodintro
      iexists s + n
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [ite_true] at Hcredit
      rw [int_pred s hs]
      twp_value
      imodintro
      iexists s - 1
      iframe Hcredit
      ipureintro
      rfl

private theorem selectorCallback_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) :
    IsDistSpec (GF := GF) E pl(&(selectorCallback σ).fst #())
      (RealCoin.law σ.selectorBase) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [Parameters.selectorBase] at Hcredit
    iapply (RationalCoin.rationalCoin_distSpec E σ.factorDen σ.factorNum
      σ.factorDen_pos.le σ.factorNum_pos σ.factor_lt.le).spec F hF $$ Hcredit

private theorem power_spec (E : CoPset) (p : unitInterval) (σ : Parameters p) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.rationalPower &(selectorCallback σ).fst #int (n : ℤ) #1 #())
      (RealCoin.law (σ.selector n)) Val.bool := by
  simpa only [Nat.mul_one, Nat.cast_one, Parameters.selector, IterateCoin.law] using
    RationalPowerInteger.rationalPower_integer_distSpec E σ.selectorBase (selectorCallback σ)
      (selectorCallback_spec E p σ) n 1 (by norm_num)

private abbrev stage (E : CoPset) (p : unitInterval) (coin : Val rT)
    (σ : Parameters p) (δ : ℝ≥0∞) : IProp GF :=
  iprop(∀ s : ℕ, ∀ _ : 0 < s, ∀ F : Bool → ℝ≥0∞,
    ↯ (IterateCoin.credit σ.bias s F + δ) -∗
      tglWp E pl(&(Syntax.loop coin).fst #int (s : ℤ) #int σ.a #int σ.b
        #int σ.e #int σ.f #int σ.numerator #int σ.denominator)
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))))

private abbrev outer (E : CoPset) (p : unitInterval) (coin : Val rT)
    (δ : ℝ≥0∞) : IProp GF := iprop(∀ σ : Parameters p, stage E p coin σ (2 * δ))

private theorem twp_stage_positive (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (σ : Parameters p) (δ ζ : ℝ≥0∞) (hζ : 0 < ζ) :
    ⊢ ↯ ζ -∗ outer E p coin δ -∗ stage E p coin σ δ := by
  iintro Hstage
  iapply ErrorCredit.Induction.simple hζ σ.one_lt_terminationFactor $$ [] Hstage
  iintro !> ⟨IH, Hstage⟩ Houter %s %hs %F Hcredit
  iapply twp_loop_open E coin (s : ℤ) σ.a σ.b σ.e σ.f σ.numerator σ.denominator
  iterate 2 twp_pure
  twp_bind (drawNext coin σ s)
  icombine Hcredit Hstage as Hcredit
  ihave Hcredit := ErrorCredit.weaken (σ.expectation s hs F δ ζ) $$ Hcredit
  iapply ((drawNext_spec E p σ coin hcoin s hs).wp (fun n => σ.continuation n F δ ζ)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  twp_pure
  twp_pure
  rw [natural_zero_test]
  by_cases hn : n = 0
  · subst n
    rw [decide_eq_true rfl]
    twp_pure
    twp_value
    imodintro
    iexists true
    isimp only [Parameters.continuation, ite_true] at Hcredit
    iframe Hcredit
    itrivial
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [decide_eq_false hn]
    twp_pure
    iterate 2 twp_pure
    by_cases ho : (n : ℤ) * σ.denominator < σ.numerator
    · rw [decide_eq_true ho]
      twp_pure
      isimp only [Parameters.continuation, ite_eq_right hn, Parameters.ordinary,
        hnpos, ho, and_self, ite_true] at Hcredit
      ihave ⟨Hcredit, Hstage⟩ := ErrorCredit.split $$ Hcredit
      iapply IH $$ Hstage Houter %n %hnpos %F Hcredit
    · rw [decide_eq_false ho]
      twp_pure
      iterate 5 twp_pure
      twp_bind pl(&Occil.FactoryExtra.rationalPower &(selectorCallback σ).fst
        #int (n : ℤ) #1 #())
      isimp only [Parameters.continuation, ite_eq_right hn, Parameters.ordinary,
        ho, and_false, ite_false] at Hcredit
      iapply ((power_spec E p σ n).wp (σ.boundaryCredit n F δ)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_value
        imodintro
        iexists false
        isimp only [Parameters.boundaryCredit, Bool.false_eq_true, ite_false] at Hcredit
        iframe Hcredit
        itrivial
      · twp_pure
        iterate 4 twp_pure
        simp only [Exp.ofVal]
        rw [next_call (Syntax.loop coin) σ (n : ℤ)]
        isimp only [Parameters.boundaryCredit, ite_true] at Hcredit
        iapply Houter $$ %σ.next %n %hnpos %F Hcredit

private theorem twp_stage (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (σ : Parameters p) (δ : ℝ≥0∞) :
    ⊢ outer E p coin δ -∗ stage E p coin σ δ := by
  iintro Houter %s %hs %F Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ζ %hζ Hstage
  iapply (twp_stage_positive E p coin hcoin σ δ ζ hζ) $$
    Hstage Houter %s %hs %F Hcredit

private theorem twp_loop_positive (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ⊢ ↯ δ -∗ ∀ σ : Parameters p, ∀ s : ℕ, ∀ _ : 0 < s, ∀ F : Bool → ℝ≥0∞,
      ↯ (IterateCoin.credit σ.bias s F) -∗
        tglWp E pl(&(Syntax.loop coin).fst #int (s : ℤ) #int σ.a #int σ.b
          #int σ.e #int σ.f #int σ.numerator #int σ.denominator)
          (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple hδ (by norm_num : (1 : ℝ≥0) < 2) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %σ %s %hs %F Hcredit
  isimp only [two_coe] at IH
  ihave Houter : outer E p coin δ $$ [IH]
  · iintro %τ %n %hn %G Hnext
    ihave ⟨Hnext, Hterm⟩ := ErrorCredit.split $$ Hnext
    iapply IH $$ Hterm %τ %n %hn %G Hnext
  icombine Hcredit Hterm as Hcredit
  iapply (twp_stage E p coin hcoin σ δ) $$ Houter %s %hs %F Hcredit

/-- Geometric jumps preserve the power law, with separate induction at each stage. -/
theorem twp_loop (E : CoPset) (p : unitInterval) (σ : Parameters p) (s : ℕ) (hs : 0 < s)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (IterateCoin.credit σ.bias s F) -∗
      tglWp E pl(&(Syntax.loop coin).fst #int (s : ℤ) #int σ.a #int σ.b
        #int σ.e #int σ.f #int σ.numerator #int σ.denominator)
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  iapply (twp_loop_positive E p coin hcoin δ hδ) $$ Hterm %σ %s %hs %F Hcredit

end specification

end

end SampLib.Linear2014
