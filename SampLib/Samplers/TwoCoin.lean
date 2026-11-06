import SampLib.SamplerStep
import SampLib.Distributions.BernoulliRetry
import SampLib.Samplers.RationalCoin
import Samplers.Bernoulli.Powers

/-! # Portkey two-coin race

A selector chooses an input coin; the portkey coin also permits immediate failure.
Only rejected input trials restart the race.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.TwoCoin

set_option maxHeartbeats 600000

noncomputable section

/-- Success mass of a single trial. -/
def success (p r β : unitInterval) : ℝ := (β : ℝ) * r * p

/-- Failure mass includes the portkey's immediate exit. -/
def failure (q r β : unitInterval) : ℝ := 1 - (β : ℝ) + β * (1 - (r : ℝ)) * q

private theorem success_nonneg (p r β : unitInterval) : 0 ≤ success p r β :=
  mul_nonneg (mul_nonneg β.2.1 r.2.1) p.2.1

private theorem failure_nonneg (q r β : unitInterval) : 0 ≤ failure q r β :=
  add_nonneg (sub_nonneg.mpr β.2.2)
    (mul_nonneg (mul_nonneg β.2.1 (sub_nonneg.mpr r.2.2)) q.2.1)

/-- Accepted trials have the normalized Portkey success mass. -/
abbrev bias (p q r β : unitInterval) :=
  BernoulliRetry.bias (success p r β) (failure q r β)
    (success_nonneg p r β) (failure_nonneg q r β)

/-- Portkey success is the accepted first-side mass divided by the total exit mass. -/
theorem bias_coe (p q r β : unitInterval) :
    (bias p q r β : ℝ) = (β : ℝ) * r * p /
      (1 - (β : ℝ) + β * (r * (p : ℝ) + (1 - (r : ℝ)) * q)) := by
  change (β : ℝ) * r * p / ((β : ℝ) * r * p +
    (1 - (β : ℝ) + β * (1 - (r : ℝ)) * q)) = _
  congr 1
  ring

/-- Retry probability of one complete trial. -/
def retry (p q r β : unitInterval) : unitInterval :=
  ⟨(β : ℝ) * (r * (1 - (p : ℝ)) + (1 - (r : ℝ)) * (1 - (q : ℝ))),
    mul_nonneg β.2.1 (add_nonneg (mul_nonneg r.2.1 (sub_nonneg.mpr p.2.2))
      (mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr q.2.2))),
    by
      have h₁ := mul_nonneg r.2.1 p.2.1
      have h₂ := mul_nonneg (sub_nonneg.mpr r.2.2) q.2.1
      have hm : (r : ℝ) * (1 - (p : ℝ)) + (1 - (r : ℝ)) * (1 - (q : ℝ)) ≤ 1 := by
        nlinarith
      calc
        _ ≤ (β : ℝ) * 1 := mul_le_mul_of_nonneg_left hm β.2.1
        _ ≤ 1 := by simpa using β.2.2⟩

@[simp] private theorem retry_coe (p q r β : unitInterval) :
    (retry p q r β : ℝ) = (β : ℝ) *
      (r * (1 - (p : ℝ)) + (1 - (r : ℝ)) * (1 - (q : ℝ))) := rfl

private theorem trial_partition (p q r β : unitInterval) :
    success p r β + failure q r β + (retry p q r β : ℝ) = 1 := by
  dsimp [success, failure, retry]
  ring

private theorem retry_lt_one (p q r β : unitInterval)
    (h : 0 < success p r β + failure q r β) : (retry p q r β : ℝ) < 1 := by
  linarith [trial_partition p q r β]

def inputCredit (p q r β : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (side accepted : Bool) : ℝ≥0∞ :=
  if accepted then F side else RealCoin.credit (bias p q r β) F +
    BernoulliRetry.factor (retry p q r β) * ε

def choiceCredit (p q r β : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (side : Bool) : ℝ≥0∞ :=
  if side then ∫⁻ b, inputCredit p q r β F ε true b ∂RealCoin.law p
  else ∫⁻ b, inputCredit p q r β F ε false b ∂RealCoin.law q

def portkeyCredit (p q r β : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (proceed : Bool) : ℝ≥0∞ :=
  if proceed then ∫⁻ side, choiceCredit p q r β F ε side ∂RealCoin.law r else F false

/-- Partition one trial into its two exits and its retry event. -/
theorem expectation (p q r β : unitInterval) (h : 0 < success p r β + failure q r β)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, portkeyCredit p q r β F ε b ∂RealCoin.law β ≤
      RealCoin.credit (bias p q r β) F + ε := by
  have hf₁ := sub_nonneg.mpr β.2.2
  have hf₂ := mul_nonneg (mul_nonneg β.2.1 (sub_nonneg.mpr r.2.2)) q.2.1
  calc
    _ = ofReal (success p r β) * F true + ofReal (failure q r β) * F false +
        ofReal (retry p q r β : ℝ) *
          (RealCoin.credit (bias p q r β) F + BernoulliRetry.factor (retry p q r β) * ε) := by
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
        portkeyCredit, choiceCredit, inputCredit, ite_true, Bool.false_eq_true, ite_false]
      rw [show failure q r β = 1 - (β : ℝ) + β * (1 - (r : ℝ)) * q from rfl,
        ENNReal.ofReal_add hf₁ hf₂]
      simp only [success, retry_coe, ofReal_mul β.2.1, ofReal_mul r.2.1,
        ENNReal.ofReal_add (mul_nonneg r.2.1 (sub_nonneg.mpr p.2.2))
          (mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr q.2.2)),
        ofReal_mul (sub_nonneg.mpr r.2.2),
        ofReal_mul (mul_nonneg β.2.1 r.2.1),
        ofReal_mul (mul_nonneg β.2.1 (sub_nonneg.mpr r.2.2))]
      ring
    _ ≤ _ := BernoulliRetry.expectation _ _ (success_nonneg p r β)
      (failure_nonneg q r β) (retry p q r β) (retry_lt_one p q r β h)
      (trial_partition p q r β) F ε


private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.twoCoin, .fix (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.twoCoin := rfl

private theorem guard_false (x y : ℕ) (hxy : 0 < x + y) :
    decide ((x : ℤ) + y ≤ 0) = false := by
  exact decide_eq_false (by exact_mod_cast not_le.mpr hxy)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE proof with abstract contracts for the two rational selectors. -/
theorem twp_twoCoin (E : CoPset) (p q r β : unitInterval)
    (h : 0 < success p r β + failure q r β) (x y a b : ℕ) (hxy : 0 < x + y)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (hportkey : IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (a : ℤ) #int (b : ℤ)) (RealCoin.law β) Val.bool)
    (hchoose : IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (x : ℤ) #int ((x + y : ℕ) : ℤ)) (RealCoin.law r) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias p q r β) F) -∗
      tglWp E pl(&Occil.FactoryExtra.twoCoin &left.fst &right.fst
        #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (BernoulliRetry.one_lt_factor (retry p q r β) (retry_lt_one p q r β h)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  rw [← source_fst (rT := rT)]
  iterate 8 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
    Var.internal.injEq, ProbLang.openRec_val_fst, RationalCoin.rationalCoin_openRec,
    RationalCoin.rationalCoin_closeRec])
  twp_pures
  rw [guard_false x y hxy, Bool.or_false]
  twp_pure
  twp_bind pl(&Occil.rationalCoin #int (a : ℤ) #int (b : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation p q r β h F ε) $$ Hcredit
  iapply (hportkey.wp (portkeyCredit p q r β F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %proceed Hcredit
  cases proceed
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [portkeyCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iterate 2 twp_pure
    simp only [← Int.natCast_add]
    twp_bind pl(&Occil.rationalCoin #int (x : ℤ) #int ((x + y : ℕ) : ℤ))
    isimp only [portkeyCredit, ite_true] at Hcredit
    iapply (hchoose.wp (choiceCredit p q r β F ε) (measurable_of_countable _) _) $$ Hcredit
    iintro %side Hcredit
    cases side
    · twp_pure
      twp_bind pl(&right.fst #())
      isimp only [choiceCredit, Bool.false_eq_true, ite_false] at Hcredit
      iapply (hright.wp (inputCredit p q r β F ε false) (measurable_of_countable _) _)
        $$ Hcredit
      iintro %accepted Hcredit
      cases accepted
      · twp_pure
        isimp only [inputCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(source (rT := rT)).fst &left.fst &right.fst
          #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm Hcredit
      · twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [inputCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial
    · twp_pure
      twp_bind pl(&left.fst #())
      isimp only [choiceCredit, ite_true] at Hcredit
      iapply (hleft.wp (inputCredit p q r β F ε true) (measurable_of_countable _) _) $$ Hcredit
      iintro %accepted Hcredit
      cases accepted
      · twp_pure
        isimp only [inputCredit, Bool.false_eq_true, ite_false] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        twp_bind pl(&(source (rT := rT)).fst &left.fst &right.fst
          #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hterm Hcredit
      · twp_pures
        twp_value
        imodintro
        iexists true
        isimp only [inputCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial

variable [ProbLangDist.IsUniformInt rT]

/-- The probability of choosing the first input coin. -/
def weightBias (x y : ℕ) (hxy : 0 < x + y) : unitInterval :=
  RationalCoin.bias (x : ℤ) ((x + y : ℕ) : ℤ)
    (by omega) (by exact_mod_cast hxy) (by omega)

/-- The probability of continuing past the portkey gate. -/
def portkeyBias (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) : unitInterval :=
  RationalCoin.bias a b (by omega) (by exact_mod_cast hb) (by exact_mod_cast hab)

/-- The exact Portkey law, including a zero portkey bias and absent weighted sides. -/
theorem twoCoin_distSpec (E : CoPset) (p q : unitInterval) (x y a b : ℕ)
    (hxy : 0 < x + y) (hb : 0 < b) (hab : a ≤ b)
    (h : 0 < success p (weightBias x y hxy) (portkeyBias a b hb hab) +
      failure q (weightBias x y hxy) (portkeyBias a b hb hab)) (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.twoCoin &left.fst &right.fst
        #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias p q (weightBias x y hxy) (portkeyBias a b hb hab))) Val.bool where
  spec F _ := by
    have hchoose := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E (x : ℤ) ((x + y : ℕ) : ℤ) (by omega) (by exact_mod_cast hxy) (by omega)
    have hportkey := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E a b (by omega) (by exact_mod_cast hb) (by exact_mod_cast hab)
    simpa only [RealCoin.lintegral_law] using wand_entails
      (twp_twoCoin E p q (weightBias x y hxy) (portkeyBias a b hb hab)
        h x y a b hxy left right hleft hright hportkey hchoose F)

end specification

end

end SampLib.TwoCoin
