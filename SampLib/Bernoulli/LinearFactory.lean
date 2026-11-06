import SampLib.Bernoulli.Laws.LinearFactory
import SampLib.Core.SupportedSpec
import SampLib.Core.SamplerStep

/-! # Huber's adaptive linear factory

The geometric-sum invariant handles the finite inner loop. The supplied margin
then bounds the expected number of immediate recursive factory calls strictly below one.
-/

open Set ProbLang
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.LinearFactory

noncomputable section

set_option maxHeartbeats 800000

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.linear, .fix (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.linear := rfl

private def retry {rT : Type _} (factory coin : Val rT) {p : unitInterval}
    (σ : Parameters p) : Val rT :=
  ⟨.fix (.lam (pl% if &factory.fst &coin.fst #int σ.a #int σ.b #int σ.e #int σ.f #()
    then if &Occil.FactoryExtra.highPowerLogistic &coin.fst ({Exp.bvar 0} - #2)
      #int σ.a #int σ.b then #true else {Exp.bvar 1} ({Exp.bvar 0} - #1)
    else #false)), .fix (by is_lc), by is_lc⟩

private theorem highPowerLogistic_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.highPowerLogistic = Occil.FactoryExtra.highPowerLogistic :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem highPowerLogistic_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.highPowerLogistic : Exp rT) =
      Occil.FactoryExtra.highPowerLogistic :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.highPowerLogistic, Occil.logisticFactory,
      Exp.fv, RationalCoin.rationalCoin_fv])

private theorem gambler_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.gambler = Occil.FactoryExtra.gambler :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem gambler_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.gambler : Exp rT) = Occil.FactoryExtra.gambler :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.gambler, Occil.logisticFactory,
      Exp.fv, RationalCoin.rationalCoin_fv])

private theorem valid_test {p : unitInterval} (σ : Parameters p) :
    (decide (σ.a < 0) || decide (σ.b ≤ 0)) = false := by
  simp [not_lt.mpr σ.admissible.1, not_le.mpr σ.admissible.2.1]

private theorem margin_test {p : unitInterval} (σ : Parameters p) (h : σ.b < σ.a) :
    (decide (σ.e ≤ 0) || decide (σ.f ≤ σ.e)) = false := by
  obtain ⟨he, hef, _⟩ := σ.admissible.2.2 h
  simp [not_le.mpr he, not_le.mpr hef]

private theorem int_height (n : ℕ) : (n : ℤ) + 1 + 2 - 2 = (n + 1 : ℕ) := by omega

private theorem int_height_pred (n : ℕ) : (n : ℤ) + 1 + 2 - 1 = (n + 2 : ℕ) := by
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

variable [ProbLangDist.IsUniformInt rT]

/-- A finite loop uses its recursive factory contract once per attempted height. -/
private theorem twp_retry (E : CoPset) (p : unitInterval) (σ : Parameters p) (ha : 0 < σ.a)
    (factory coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (δ : ℝ≥0∞) (n : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ □ (∀ G : Bool → ℝ≥0∞, ↯ (RealCoin.credit σ.bias G + δ) -∗
        tglWp E pl(&factory.fst &coin.fst #int σ.a #int σ.b #int σ.e #int σ.f #())
          (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (G z)))) -∗
      ↯ (RealCoin.credit (innerBias σ.bias n) F + ofReal (calls σ.bias n) * δ) -∗
      tglWp E pl(&(retry factory coin σ).fst #int ((n + 2 : ℕ) : ℤ))
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  induction n with
  | zero =>
    have hpower := HighPowerLogistic.highPowerLogistic_base_distSpec
      (rT := rT) (GF := GF) E coin 0 σ.a σ.b le_rfl
    iintro #Hfactory Hcredit
    iterate 2 (twp_step; simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst,
      highPowerLogistic_openRec])
    twp_bind pl(&factory.fst &coin.fst #int σ.a #int σ.b #int σ.e #int σ.f #())
    ihave Hcredit := ErrorCredit.weaken (le_of_eq (inner_expectation σ.bias F δ 0)) $$ Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply Hfactory $$ %(factoryCredit σ.bias F δ 0) Hcredit
    iintro %v ⟨%z, %hv, Hcredit⟩
    subst v
    cases z
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [factoryCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      twp_bind pl(&Occil.FactoryExtra.highPowerLogistic &coin.fst #0 #int σ.a #int σ.b)
      isimp only [factoryCredit, ite_true, powerBias_zero] at Hcredit
      iapply (hpower.wp_supported (fun z => z = true) (Set.to_countable _).measurableSet
          (by simp [RealCoin.law, RealCoin.pmf])
          (powerCredit σ.bias F δ 0) (measurable_of_countable _) _) $$ Hcredit
      iintro %z %hz Hcredit
      subst z
      twp_pure
      twp_value
      imodintro
      iexists true
      isimp only [powerCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  | succ n IH =>
    have hpower : IsDistSpec (GF := GF) E
        pl(&Occil.FactoryExtra.highPowerLogistic &coin.fst #int ((n + 1 : ℕ) : ℤ)
          #int σ.a #int σ.b) (RealCoin.law (powerBias σ.bias (n + 1))) Val.bool :=
      HighPowerLogistic.highPowerLogistic_distSpec E p (n + 1) σ.a σ.b ha
        σ.admissible.2.1 coin hcoin
    iintro #Hfactory Hcredit
    iterate 2 (twp_step; simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst,
      highPowerLogistic_openRec])
    twp_bind pl(&factory.fst &coin.fst #int σ.a #int σ.b #int σ.e #int σ.f #())
    ihave Hcredit := ErrorCredit.weaken (le_of_eq (inner_expectation σ.bias F δ (n + 1)))
      $$ Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply Hfactory $$ %(factoryCredit σ.bias F δ (n + 1)) Hcredit
    iintro %v ⟨%z, %hv, Hcredit⟩
    subst v
    cases z
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [factoryCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      rw [int_height]
      twp_bind pl(&Occil.FactoryExtra.highPowerLogistic &coin.fst
        #int ((n + 1 : ℕ) : ℤ) #int σ.a #int σ.b)
      isimp only [factoryCredit, ite_true] at Hcredit
      iapply (hpower.wp (powerCredit σ.bias F δ (n + 1)) (measurable_of_countable _) _)
        $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_pure
        rw [int_height_pred]
        isimp only [powerCredit, Bool.false_eq_true, ite_false, retryCredit,
          Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at Hcredit
        twp_bind pl(&(retry factory coin σ).fst #int ((n + 2 : ℕ) : ℤ))
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hfactory Hcredit
      · twp_pure
        twp_value
        imodintro
        iexists true
        isimp only [powerCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial

/-- Every recursive parameter tuple receives the same amplified ambient slack. -/
private theorem twp_positive (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ↯ ε -∗ ∀ σ : Parameters p, ∀ F : Bool → ℝ≥0∞,
      ↯ (RealCoin.credit σ.bias F) -∗
      tglWp E pl(&(source (rT := rT)).fst &coin.fst #int σ.a #int σ.b #int σ.e #int σ.f #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hterm
  iapply ErrorCredit.Induction.amplifying hε (by norm_num : (1 : ℝ≥0) < 2) $$ [] Hterm
  iintro !> %δ %hδ #IH Hterm %σ %F Hcredit
  iterate 7 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
    Var.internal.injEq, ProbLang.openRec_val_fst, gambler_openRec, gambler_closeRec,
    highPowerLogistic_openRec, highPowerLogistic_closeRec,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec])
  twp_pures
  rw [valid_test σ]
  twp_pure
  twp_pure
  by_cases hc : σ.a ≤ σ.b
  · have hselect := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E σ.a σ.b σ.admissible.1 σ.admissible.2.1 hc
    rw [decide_eq_true hc]
    twp_pure
    twp_bind pl(&Occil.rationalCoin #int σ.a #int σ.b)
    isimp only [← contracting_expectation σ hc F] at Hcredit
    iapply (hselect.wp (contractingCredit p F) (measurable_of_countable _) _) $$ Hcredit
    iintro %z Hcredit
    cases z
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [contractingCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [contractingCredit, ite_true] at Hcredit
      iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit
  · have h : σ.b < σ.a := lt_of_not_ge hc
    have hs : IsDistSpec (GF := GF) E
        pl(&Occil.rationalCoin #int (scale σ.e σ.f - 1) #int (scale σ.e σ.f))
        (RealCoin.law (σ.selector h)) Val.bool :=
      RationalCoin.rationalCoin_distSpec E _ _
        (σ.selector_bounds h).1 (σ.selector_bounds h).2.1 (σ.selector_bounds h).2.2
    have hw : IsDistSpec (GF := GF) E
        pl(&Occil.FactoryExtra.gambler &coin.fst #int ((σ.height : ℕ) : ℤ)
          #int (σ.next h).a #int (σ.next h).b) (RealCoin.law (σ.walkBias h)) Val.bool :=
      Gambler.gambler_distSpec E p σ.height (σ.next h).a (σ.next h).b
        (σ.next_a_pos h) (σ.next h).admissible.2.1 coin hcoin
    simp only [σ.height_cast h, Parameters.next_a, Parameters.next_b] at hw
    have hr := twp_retry E p (σ.next h) (σ.next_a_pos h) (source (rT := rT)) coin hcoin
      (2 * δ) (σ.height - 2) F
    simp only [retry, Nat.sub_add_cancel (σ.height_two h), σ.height_cast h,
      Parameters.next_a, Parameters.next_b, Parameters.next_e, Parameters.next_f] at hr
    rw [decide_eq_false hc]
    twp_pure
    twp_pures
    rw [margin_test σ h]
    twp_pure
    iterate 19 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.ofVal,
      ProbLang.openRec_val_fst, gambler_openRec, highPowerLogistic_openRec,
      RationalCoin.rationalCoin_openRec])
    simp only [scale_pred, sub_add_cancel]
    twp_bind pl(&Occil.FactoryExtra.gambler &coin.fst #int (scale σ.e σ.f)
      #int (σ.a * scale σ.e σ.f) #int (σ.b * (scale σ.e σ.f - 1)))
    icombine Hcredit Hterm as Hcredit
    ihave Hcredit := ErrorCredit.weaken (expectation σ h F δ) $$ Hcredit
    iapply (hw.wp (walkCredit σ h F δ) (measurable_of_countable _) _) $$ Hcredit
    iintro %z Hcredit
    cases z
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [walkCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      twp_bind pl(&Occil.rationalCoin #int (scale σ.e σ.f - 1) #int (scale σ.e σ.f))
      isimp only [walkCredit, ite_true] at Hcredit
      iapply (hs.wp (selectorCredit σ h F δ) (measurable_of_countable _) _) $$ Hcredit
      iintro %z Hcredit
      cases z
      · twp_pure
        twp_step
        simp [Exp.open', Exp.openRec]
        isimp only [selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave #Hfactory : □ (∀ G : Bool → ℝ≥0∞,
          ↯ (RealCoin.credit (σ.next h).bias G + 2 * δ) -∗
            tglWp E pl(&(source (rT := rT)).fst &coin.fst
              #int (σ.next h).a #int (σ.next h).b #int (σ.next h).e #int (σ.next h).f #())
              (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (G z)))) $$ []
        · iintro !> %G Hcredit
          ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
          iapply IH $$ Hterm %(σ.next h) %G Hcredit
        isimp only [Parameters.next_a, Parameters.next_b,
          Parameters.next_e, Parameters.next_f] at Hfactory
        iapply hr $$ Hfactory Hcredit
      · twp_pure
        twp_value
        imodintro
        iexists true
        isimp only [selectorCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial

/-- CTE verification over the complete conditional-margin parameter domain. -/
theorem twp_linear (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p a b e f h) F) -∗
      tglWp E pl(&Occil.FactoryExtra.linear &coin.fst #int a #int b #int e #int f #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  unfold bias
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  rw [← source_fst (rT := rT)]
  iapply (twp_positive E p coin hcoin ε hε) $$ Hterm %(Parameters.mk a b e f h) %F Hcredit

/-- Exact linear Bernoulli law, including zero and contracting coefficients. -/
theorem linear_distSpec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linear &coin.fst #int a #int b #int e #int f #())
      (RealCoin.law (bias p a b e f h)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails (twp_linear E p a b e f h coin hcoin F)

end specification

end

end SampLib.LinearFactory
