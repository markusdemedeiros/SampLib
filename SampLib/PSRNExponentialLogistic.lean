import SampLib.Samplers.LogisticFactory
import SampLib.Samplers.FairCoin
import SampLib.CurriedStep

/-! # The actual exponential digit callback

A fair selector returns false or tries the decay callback. A failed decay trial
retries, giving success probability `q/(1+q)` and at most one-half retry mass.
The raw syntax inserts callbacks after closing binders, retaining their variables.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.ExponentialLogistic

noncomputable section

def bias (q : unitInterval) : unitInterval :=
  LogisticFactory.bias q VonNeumann.fairBias (by norm_num [VonNeumann.fairBias])

theorem bias_coe (q : unitInterval) : (bias q : ℝ) = (q : ℝ) / (1 + q) := by
  simp only [bias, LogisticFactory.bias, VonNeumann.fairBias]
  field_simp
  ring

namespace Program

/-- Body beneath the fixpoint and unit binders; both external operands are closed. -/
def body {rT : Type} (decay denominator : Exp rT) : Exp rT :=
  .cond (.app Occil.fairCoin (.lit .unit)) (.lit (.bool false))
    (.cond (.app decay (.binop .mult denominator (.lit (.int 2))))
      (.lit (.bool true)) (.app (.bvar 1) (.lit .unit)))

def loopCode {rT : Type} (decay denominator : Exp rT) : Exp rT :=
  .fix (.lam (body decay denominator))

def loopVal {rT : Type} (decay : Val rT) (denominator : ℤ) : Val rT := by
  have hdecay (k : ℕ) : Exp.lcb k decay.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb decay.lc) (Nat.zero_le k)
  have hfair (k : ℕ) : Exp.lcb k (Occil.fairCoin : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb FairCoin.fairCoin_lc) (Nat.zero_le k)
  have hc : (loopCode decay.fst (.lit (.int denominator))).IsLocallyClosed := by
    apply Exp.lcb_imp_lc
    simp [loopCode, body, Exp.lcb, hdecay, hfair]
  exact ⟨loopCode decay.fst (.lit (.int denominator)), .fix hc, hc⟩

theorem opened {rT : Type} (decay : Val rT) (denominator : ℤ) :
    CurriedStep.opened [Val.unit]
      (Exp.openRec 1 (loopVal decay denominator).fst
        (body decay.fst (.lit (.int denominator)))) =
      .cond (.app Occil.fairCoin (.lit .unit)) (.lit (.bool false))
        (.cond (.app decay.fst (.binop .mult (.lit (.int denominator)) (.lit (.int 2))))
          (.lit (.bool true)) (.app (loopVal decay denominator).fst (.lit .unit))) := by
  have hopen (k : ℕ) (e : Exp rT) (v : Val rT) : Exp.openRec k e v.fst = v.fst :=
    (Exp.open_lc k e v.fst v.lc).symm
  simp only [CurriedStep.opened, body, Exp.openRec, ite_true,
    FairCoin.fairCoin_openRec, hopen]

/-- The two argument binders and the source's lexical `let logistic`. -/
def digitBody {rT : Type} (decay : Exp rT) : Exp rT :=
  .app (.lam (.app (.bvar 0) (.lit .unit))) (loopCode decay (.bvar 2))

def digitVal {rT : Type} (decay : Val rT) : Val rT := by
  have hd (k : ℕ) : Exp.lcb k decay.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb decay.lc) (Nat.zero_le k)
  have hf (k : ℕ) : Exp.lcb k (Occil.fairCoin : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb FairCoin.fairCoin_lc) (Nat.zero_le k)
  have hc : (Exp.lam (.lam (digitBody decay.fst))).IsLocallyClosed := by
    apply Exp.lcb_imp_lc
    simp [digitBody, loopCode, body, Exp.lcb, hd, hf]
  exact ⟨.lam (.lam (digitBody decay.fst)), .lam hc, hc⟩

theorem digit_opened {rT : Type} (decay : Val rT) (seen denominator : ℤ) :
    CurriedStep.opened [Val.int seen, Val.int denominator] (digitBody decay.fst) =
      .app (.lam (.app (.bvar 0) (.lit .unit))) (loopVal decay denominator).fst := by
  have hopen (k : ℕ) (e : Exp rT) (v : Val rT) : Exp.openRec k e v.fst = v.fst :=
    (Exp.open_lc k e v.fst v.lc).symm
  simp [CurriedStep.opened, digitBody, loopCode, body, Exp.openRec,
    FairCoin.fairCoin_openRec, hopen, loopVal]

/-- The literal digit callback, with the captured decay supplied after static closure. -/
def sourceTemplate {rT : Type} : Exp rT := pl%
  fun decay, fun seen denominator,
    let logistic := (rec trial u :=
      if &Occil.fairCoin #() then #false else
        if decay (denominator * #2) then #true else trial #());
    logistic #()

theorem source_eq {rT : Type} (decay : Val rT) :
    (match (sourceTemplate : Exp rT) with
      | .lam body => Exp.open' body decay.fst
      | _ => .fail) = (digitVal decay).fst := by
  simp [sourceTemplate, digitVal, digitBody, loopCode, body, Exp.open', Exp.openRec,
    Exp.close, Exp.closeRec, Var.internal.injEq, FairCoin.fairCoin_closeRec,
    FairCoin.fairCoin_openRec]

end Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem fair_pos : 0 < (VonNeumann.fairBias : ℝ) := by
  norm_num [VonNeumann.fairBias]

private theorem fair_lt_one : (VonNeumann.fairBias : ℝ) < 1 := by
  norm_num [VonNeumann.fairBias]

private theorem one_lt_factor :
    1 < LogisticFactory.terminationFactor VonNeumann.fairBias := by
  change (1 : ℝ) < 1 / (1 - 1 / 2)
  norm_num

private theorem expectation (q : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ b, LogisticFactory.selectorCredit q VonNeumann.fairBias fair_pos F ε b
      ∂RealCoin.law VonNeumann.fairBias) ≤ RealCoin.credit (bias q) F + ε :=
  LogisticFactory.expectation_preservation q VonNeumann.fairBias fair_pos fair_lt_one F ε

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_open (E : CoPset) (decay : Val rT) (denominator : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E
      (.cond (.app Occil.fairCoin (.lit .unit)) (.lit (.bool false))
        (.cond (.app decay.fst (.binop .mult (.lit (.int denominator)) (.lit (.int 2))))
          (.lit (.bool true)) (.app (Program.loopVal decay denominator).fst (.lit .unit)))) Φ ⊢
      tglWp E pl(&(Program.loopVal decay denominator).fst #()) Φ := by
  have hbody : Exp.lcb 2 (Program.body decay.fst (.lit (.int denominator))) = true := by
    have hd := Exp.lcb_mono (Exp.lc_imp_lcb decay.lc) (by decide : 0 ≤ 2)
    have hf := Exp.lcb_mono (Exp.lc_imp_lcb (FairCoin.fairCoin_lc (rT := rT)))
      (by decide : 0 ≤ 2)
    simp [Program.body, Exp.lcb, hd, hf]
  have hopen := CurriedStep.twp_fix_apply (rT := rT) (GF := GF) E [] Val.unit []
    (Program.body decay.fst (.lit (.int denominator))) hbody
    Φ
  change tglWp E (CurriedStep.opened [Val.unit]
      (Exp.openRec 1 (Program.loopVal decay denominator).fst
        (Program.body decay.fst (.lit (.int denominator))))) _ ⊢
    tglWp E pl(&(Program.loopVal decay denominator).fst #()) _ at hopen
  rw [Program.opened] at hopen
  exact hopen

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_digit_open (E : CoPset) (decay : Val rT) (seen denominator : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(Program.loopVal decay denominator).fst #()) Φ ⊢
      tglWp E pl(&(Program.digitVal decay).fst #int seen #int denominator) Φ := by
  iintro H
  have hd (k : ℕ) : Exp.lcb k decay.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb decay.lc) (Nat.zero_le k)
  have hf (k : ℕ) : Exp.lcb k (Occil.fairCoin : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb FairCoin.fairCoin_lc) (Nat.zero_le k)
  have hc : Exp.lcb 2 (Program.digitBody decay.fst) = true := by
    simp [Program.digitBody, Program.loopCode, Program.body, Exp.lcb, hd, hf]
  have hopen := CurriedStep.twp_apply (rT := rT) (GF := GF) E []
    [Val.int seen, Val.int denominator] (Program.digitBody decay.fst) hc
    Φ
  change tglWp E (CurriedStep.opened [Val.int seen, Val.int denominator]
      (Program.digitBody decay.fst)) _ ⊢
    tglWp E pl(&(Program.digitVal decay).fst #int seen #int denominator) _ at hopen
  rw [Program.digit_opened] at hopen
  iapply hopen
  twp_pure
  iapply H

private theorem credit_eq (q : unitInterval) (F : Bool → ℝ≥0∞) :
    LogisticFactory.credit q VonNeumann.fairBias fair_pos F = RealCoin.credit (bias q) F := rfl

/-- The source loop uses a fair selector and the specified decay call at twice the denominator. -/
theorem twp_loop (E : CoPset) (q : unitInterval) (decay : Val rT) (denominator : ℤ)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #int (denominator * 2))
      (RealCoin.law q) Val.bool) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias q) F) -∗
      tglWp E pl(&(Program.loopVal decay denominator).fst #())
        (fun v => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε one_lt_factor $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iapply twp_open E decay denominator
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation q F ε) $$ Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp
    (LogisticFactory.selectorCredit q VonNeumann.fairBias fair_pos F ε)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pure
    twp_pure
    twp_bind pl(&decay.fst #int (denominator * 2))
    isimp only [LogisticFactory.selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hdecay.wp (LogisticFactory.inputCredit q VonNeumann.fairBias fair_pos F ε)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %a Hcredit
    cases a
    · twp_pure
      isimp only [LogisticFactory.inputCredit, Bool.false_eq_true, ite_false, credit_eq] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      iapply IH $$ Hterm Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [LogisticFactory.inputCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [LogisticFactory.selectorCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Both source arguments are consumed before entering the unchanged retry loop. -/
theorem digit_distSpec (E : CoPset) (q : unitInterval) (decay : Val rT)
    (seen denominator : ℤ)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #int (denominator * 2))
      (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(Program.digitVal decay).fst #int seen #int denominator)
      (RealCoin.law (bias q)) Val.bool where
  spec F _ := by
    iintro Hcredit
    iapply twp_digit_open E decay seen denominator
    isimp only [RealCoin.lintegral_law] at Hcredit
    iapply twp_loop E q decay denominator hdecay F $$ Hcredit

end specification

end

end SampLib.ExponentialLogistic
