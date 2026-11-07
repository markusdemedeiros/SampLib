import SampLib.Core.Retry
import SampLib.Core.SamplerStep
import SampLib.Bernoulli.Laws.TwoCoin
import SampLib.Uniform.RationalCoin
import Samplers.Bernoulli.Powers

/-! # Portkey two-coin race

A selector chooses an input coin; the portkey coin also permits immediate failure.
Only rejected input trials restart the race.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.TwoCoin

noncomputable section

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
  iapply Retry.twp_loop solve_not_value
    (BernoulliRetry.one_lt_factor (retry p q r β) (retry_lt_one p q r β h))
  iintro !> %ε %hε IH Hcredit
  rw [← source_fst (rT := rT)]
  iterate 8 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
    Var.internal.injEq, ProbLang.openRec_val_fst, RationalCoin.rationalCoin_openRec,
    RationalCoin.rationalCoin_closeRec])
  twp_pures
  rw [guard_false x y hxy, Bool.or_false]
  twp_pure
  twp_bind pl(&Occil.rationalCoin #int (a : ℤ) #int (b : ℤ))
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
        twp_bind pl(&(source (rT := rT)).fst &left.fst &right.fst
          #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hcredit
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
        twp_bind pl(&(source (rT := rT)).fst &left.fst &right.fst
          #int (x : ℤ) #int (y : ℤ) #int (a : ℤ) #int (b : ℤ) #())
        iapply (tglWp_mono fun _ => tglWp_value)
        iapply IH $$ Hcredit
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
