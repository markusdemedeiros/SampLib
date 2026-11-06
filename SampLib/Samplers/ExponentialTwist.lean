import SampLib.SamplerStep
import SampLib.Samplers.SigmoidRational
import SampLib.Distributions.BernoulliRetry

/-! # Exponential tilting of an input coin

Keep a pair precisely when the input bit agrees with an independent logistic
selector. The accepted odds multiply the input odds by the exponential tilt.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.ExponentialTwist

noncomputable section

set_option maxHeartbeats 300000

/-- The two accepted masses determine the normalized output bias. -/
def bias (p : unitInterval) (a b : ℤ) : unitInterval :=
  BernoulliRetry.bias ((p : ℝ) * SigmoidRational.bias a b)
    ((1 - (p : ℝ)) * (1 - (SigmoidRational.bias a b : ℝ)))
    (mul_nonneg p.2.1 (SigmoidRational.bias a b).2.1)
    (mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr (SigmoidRational.bias a b).2.2))

private theorem selector_pos (a b : ℤ) : 0 < (SigmoidRational.bias a b : ℝ) := by
  exact one_div_pos.mpr (by positivity)

private theorem selector_lt_one (a b : ℤ) : (SigmoidRational.bias a b : ℝ) < 1 := by
  exact (div_lt_one (by positivity)).mpr (by linarith [Real.exp_pos (-(a : ℝ) / b)])

private theorem accepted_pos (p : unitInterval) (a b : ℤ) :
    0 < (p : ℝ) * SigmoidRational.bias a b +
      (1 - (p : ℝ)) * (1 - (SigmoidRational.bias a b : ℝ)) := by
  by_cases hp : (p : ℝ) = 0
  · simp [hp, sub_pos.mpr (selector_lt_one a b)]
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne p.2.1 (Ne.symm hp))
      (selector_pos a b))
      (mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr (SigmoidRational.bias a b).2.2))

private def retry (p : unitInterval) (a b : ℤ) : unitInterval :=
  ⟨(p : ℝ) * (1 - (SigmoidRational.bias a b : ℝ)) +
      (1 - (p : ℝ)) * SigmoidRational.bias a b,
    add_nonneg (mul_nonneg p.2.1 (sub_nonneg.mpr (SigmoidRational.bias a b).2.2))
      (mul_nonneg (sub_nonneg.mpr p.2.2) (SigmoidRational.bias a b).2.1), by
        have h := accepted_pos p a b
        nlinarith⟩

private theorem retry_lt_one (p : unitInterval) (a b : ℤ) : (retry p a b : ℝ) < 1 := by
  have h := accepted_pos p a b
  dsimp [retry]
  nlinarith

/-- The accepted odds are the input odds multiplied by `exp(a/b)`. -/
theorem coe_bias (p : unitInterval) (a b : ℤ) :
    (bias p a b : ℝ) = (p : ℝ) * Real.exp ((a : ℝ) / b) /
      ((p : ℝ) * Real.exp ((a : ℝ) / b) + 1 - (p : ℝ)) := by
  have hden : 0 < (p : ℝ) * Real.exp ((a : ℝ) / b) + 1 - (p : ℝ) := by
    by_cases hp : (p : ℝ) = 0
    · simp [hp]
    · have hprod := mul_pos (lt_of_le_of_ne p.2.1 (Ne.symm hp))
        (Real.exp_pos ((a : ℝ) / b))
      linarith [p.2.2]
  change _ / _ = _
  apply (div_eq_div_iff (accepted_pos p a b).ne' hden.ne').mpr
  simp only [SigmoidRational.bias, neg_div, Real.exp_neg]
  field_simp
  ring

def pairCredit (p : unitInterval) (a b : ℤ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (bit select : Bool) : ℝ≥0∞ :=
  if bit then if select then F true else
    RealCoin.credit (bias p a b) F + BernoulliRetry.factor (retry p a b) * ε
  else if select then
    RealCoin.credit (bias p a b) F + BernoulliRetry.factor (retry p a b) * ε
  else F false

def inputCredit (p : unitInterval) (a b : ℤ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (bit : Bool) : ℝ≥0∞ :=
  ∫⁻ select, pairCredit p a b F ε bit select ∂RealCoin.law (SigmoidRational.bias a b)

/-- Agreement gives the normalized tilted law; disagreement funds a retry. -/
theorem expectation (p : unitInterval) (a b : ℤ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ bit, inputCredit p a b F ε bit ∂RealCoin.law p ≤
      RealCoin.credit (bias p a b) F + ε := by
  have hsum : (p : ℝ) * SigmoidRational.bias a b +
      (1 - (p : ℝ)) * (1 - (SigmoidRational.bias a b : ℝ)) + retry p a b = 1 := by
    dsimp [retry]
    ring
  have h := BernoulliRetry.expectation
    ((p : ℝ) * SigmoidRational.bias a b)
    ((1 - (p : ℝ)) * (1 - (SigmoidRational.bias a b : ℝ)))
    (mul_nonneg p.2.1 (SigmoidRational.bias a b).2.1)
    (mul_nonneg (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr (SigmoidRational.bias a b).2.2))
    (retry p a b) (retry_lt_one p a b) hsum F ε
  change ofReal ((p : ℝ) * SigmoidRational.bias a b) * F true +
    ofReal ((1 - (p : ℝ)) * (1 - (SigmoidRational.bias a b : ℝ))) * F false +
    ofReal (retry p a b : ℝ) *
      (RealCoin.credit (bias p a b) F + BernoulliRetry.factor (retry p a b) * ε) ≤
      RealCoin.credit (bias p a b) F + ε at h
  apply le_trans (le_of_eq ?_) h
  simp only [inputCredit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    pairCredit, Bool.false_eq_true, ite_true, ite_false]
  rw [ofReal_mul p.2.1, ofReal_mul (sub_nonneg.mpr p.2.2)]
  rw [show ofReal (retry p a b : ℝ) =
    ofReal (p : ℝ) * ofReal (1 - (SigmoidRational.bias a b : ℝ)) +
      ofReal (1 - (p : ℝ)) * ofReal (SigmoidRational.bias a b : ℝ) by
        rw [retry, ofReal_add
          (mul_nonneg p.2.1 (sub_nonneg.mpr (SigmoidRational.bias a b).2.2))
          (mul_nonneg (sub_nonneg.mpr p.2.2) (SigmoidRational.bias a b).2.1),
          ofReal_mul p.2.1, ofReal_mul (sub_nonneg.mpr p.2.2)]]
  ring

private def term {rT : Type _} (selector : Val rT) : Exp rT :=
  let recur := pl(&(.bvar 6 : Exp rT) &(.bvar 5) &(.bvar 4) &(.bvar 3) #())
  .fix (.lam (.lam (.lam (.lam (
    .app (.lam (
      .app (.lam (
        .cond (.bvar 1) (.cond (.bvar 0) pl(#true) recur)
          (.cond (.bvar 0) recur pl(#false))))
        pl(&selector.fst &(.bvar 3) &(.bvar 2) #())))
      pl(&(.bvar 3) #()))))))

private def logisticSelector {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.sigmoidRational,
    .lam SigmoidRational.sigmoidRational_lc, SigmoidRational.sigmoidRational_lc⟩

private theorem implementation_eq {rT : Type _} :
    term (logisticSelector : Val rT) = Occil.FactoryExtra.exponentialTwist := by
  simp [term, logisticSelector, Occil.FactoryExtra.exponentialTwist,
    Exp.close, Exp.closeRec]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- Flip the input and selector, returning on agreement and retrying otherwise. -/
private theorem twp_term (E : CoPset) (p : unitInterval) (a b : ℤ)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (selector : Val rT)
    (hselect : IsDistSpec (GF := GF) E pl(&selector.fst #int a #int b #())
      (RealCoin.law (SigmoidRational.bias a b)) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p a b) F) -∗
      tglWp E pl(&(term selector) &coin.fst #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hopen (k : ℕ) (e : Exp rT) : Exp.openRec k e selector.fst = selector.fst :=
    (Exp.open_lc k e _ selector.lc).symm
  have hterm : (term selector).IsLocallyClosed := by is_lc
  have htermOpen (k : ℕ) (e : Exp rT) :
      Exp.openRec k e (term selector) = term selector := (Exp.open_lc k e _ hterm).symm
  have hcoinOpen (k : ℕ) (e : Exp rT) : Exp.openRec k e coin.fst = coin.fst :=
    (Exp.open_lc k e _ coin.lc).symm
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (BernoulliRetry.one_lt_factor (retry p a b) (retry_lt_one p a b)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 5
    twp_step
    simp (failIfUnchanged := false) only [Exp.open', Exp.openRec, hopen, htermOpen, hcoinOpen,
      Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation p a b F ε) $$ Htotal
  iapply (hcoin.wp (inputCredit p a b F ε) (measurable_of_countable _) _) $$ Hsample
  iintro %bit Hcredit
  twp_step
  simp (failIfUnchanged := false) only [Exp.open', Exp.openRec, hopen, htermOpen, hcoinOpen,
      Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
  twp_bind pl(&selector.fst #int a #int b #())
  isimp only [inputCredit] at Hcredit
  iapply (hselect.wp
    (pairCredit p a b F ε bit) (measurable_of_countable _) _) $$ Hcredit
  iintro %select Hcredit
  cases bit <;> cases select
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [pairCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iterate 3
      twp_step
      simp (failIfUnchanged := false) only [Exp.open', Exp.openRec, htermOpen, hcoinOpen,
        ↓reduceIte]
    isimp only [pairCredit, Bool.false_eq_true, ite_false, ite_true] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&(term selector) &coin.fst #int a #int b #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · iterate 3
      twp_step
      simp (failIfUnchanged := false) only [Exp.open', Exp.openRec, htermOpen, hcoinOpen,
        ↓reduceIte]
    isimp only [pairCredit, Bool.false_eq_true, ite_false, ite_true] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&(term selector) &coin.fst #int a #int b #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [pairCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Instantiate the agreement loop with the verified rational logistic selector. -/
theorem twp_exponentialTwist (E : CoPset) (p : unitInterval) (a b : ℤ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p a b) F) -∗
      tglWp E pl(&Occil.FactoryExtra.exponentialTwist &coin.fst #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  simpa only [implementation_eq] using twp_term E p a b coin hcoin
    logisticSelector (SigmoidRational.sigmoidRational_distSpec E a b hb) F

theorem exponentialTwist_distSpec (E : CoPset) (p : unitInterval) (a b : ℤ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.exponentialTwist &coin.fst #int a #int b #())
      (RealCoin.law (bias p a b)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_exponentialTwist E p a b hb coin hcoin F)

end specification

end

end SampLib.ExponentialTwist
