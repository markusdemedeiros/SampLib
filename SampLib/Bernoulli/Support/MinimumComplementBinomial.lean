import SampLib.Bernoulli.Laws.MinimumComplementKernel
import SampLib.Bernoulli.Laws.BernoulliEndpoints
import SampLib.Bernoulli.Support.FactoryChoose
import SampLib.Bernoulli.Support.FactoryIntegerPower
import SampLib.Discrete.Binomial
import SampLib.Uniform.RationalCoin
import SampLib.Core.Syntax.ClosedExp
import SampLib.Core.BetaStep

/-! # Padded binomial tail of the minimum-complement factory

The exact padded-binomial tail after the first-passage index is selected.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.MinimumComplement

noncomputable section

def binomialStage {rT : Type} : Exp rT := pl%
  fun coin m,
    let r := (#2 * m) / #3 + #1;
    let d := #2 * m + r;
    let heads := &Occil.binomial coin d;
    if (heads < m) || (m + r < heads) then #false else
      let numerator := &Occil.FactoryExtra.intPower #4 m *
        &Occil.FactoryExtra.choose r (heads - m);
      let denominator := #2 * &Occil.FactoryExtra.choose d heads;
      &Occil.rationalCoin numerator denominator

/-- A single binder template serves the closed source and its opened tail. -/
def bodyCode {rT : Type} (coin index : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let litInt (z : ℤ) : Exp rT := .lit (.int z)
  let call (f a b : Exp rT) := .app (.app f a) b
  let r := .binop .plus (.binop .div (.binop .mult (litInt 2) (index 0)) (litInt 3)) (litInt 1)
  let d := .binop .plus (.binop .mult (litInt 2) (index 1)) (.bvar 0)
  let heads := call Occil.binomial (coin 2) (.bvar 0)
  let outside := .binop .or (.binop .lt (.bvar 0) (index 3))
    (.binop .lt (.binop .plus (index 3) (.bvar 2)) (.bvar 0))
  let numerator := .binop .mult (call Occil.FactoryExtra.intPower (litInt 4) (index 3))
    (call Occil.FactoryExtra.choose (.bvar 2) (.binop .minus (.bvar 0) (index 3)))
  let denominator := .binop .mult (litInt 2) (call Occil.FactoryExtra.choose (.bvar 2) (.bvar 1))
  let accept := call Occil.rationalCoin (.bvar 1) (.bvar 0)
  bind r (bind d (bind heads (.cond outside (.lit (.bool false))
    (bind numerator (bind denominator accept)))))

private def stageBody {rT : Type} : Exp rT :=
  bodyCode (fun depth => .bvar (depth + 1)) (fun depth => .bvar depth)

/-- The actual source tail, after its coin and index have been supplied. -/
def binomialBody {rT : Type} (coin : Val rT) (m : ℕ) : Exp rT :=
  bodyCode (fun _ => coin.fst) (fun _ => .lit (.int (m : ℤ)))

private theorem denominator_pos (m j : ℕ) (hj : j ≤ m + padding m) :
    0 < 2 * (2 * m + padding m).choose j :=
  Nat.mul_pos (by decide) (Nat.choose_pos (by omega))

private theorem numerator_le (m j : ℕ) (hlo : m ≤ j) (hhi : j ≤ m + padding m) :
    4 ^ m * (padding m).choose (j - m) ≤ 2 * (2 * m + padding m).choose j := by
  simpa only [Nat.add_sub_of_le hlo] using
    choose_acceptance_bound m (padding m) (j - m) (padding_pos m) (padding_large m) (by omega)

private theorem acceptance_eq_ratio (m j : ℕ) (hlo : m ≤ j) (hhi : j ≤ m + padding m) :
    acceptanceBias m j = RationalCoin.bias
      ((4 ^ m * (padding m).choose (j - m) : ℕ) : ℤ)
      ((2 * (2 * m + padding m).choose j : ℕ) : ℤ)
      (by positivity) (by exact_mod_cast denominator_pos m j hhi)
      (by exact_mod_cast numerator_le m j hlo hhi) := by
  apply Subtype.ext
  simp [acceptanceBias, acceptance, hlo, hhi, RationalCoin.bias]

private theorem acceptance_eq_zero (m j : ℕ) (hband : ¬(m ≤ j ∧ j ≤ m + padding m)) :
    acceptanceBias m j = 0 := by
  apply Subtype.ext
  simp [acceptanceBias, acceptance, hband]

private theorem padding_cast (m : ℕ) : ((2 * m : ℤ) / 3 + 1) = (padding m : ℤ) := by
  simp [padding, Nat.cast_add, Nat.cast_mul]

private theorem outside_test (m j : ℕ) :
    Bool.or (decide ((j : ℤ) < m)) (decide ((m : ℤ) + padding m < j)) =
      decide (¬(m ≤ j ∧ j ≤ m + padding m)) := by
  by_cases h : m ≤ j ∧ j ≤ m + padding m <;> simp_all <;> omega

private instance binomial_closed {rT : Type} : ClosedExp (Occil.binomial : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.binomial, Exp.fv]

private instance choose_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance power_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

private instance rational_closed {rT : Type} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.rationalCoin, Exp.fv]

instance binomialStage_closed {rT : Type} : ClosedExp (binomialStage : Exp rT) where
  lc := by is_lc
  fv := by simp [binomialStage, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

theorem binomialStage_eq {rT : Type} :
    (binomialStage : Exp rT) = .lam (.lam stageBody) := by
  simp [binomialStage, stageBody, bodyCode, Exp.close, Exp.closeRec,
    Var.internal.injEq, ClosedExp.closeRec]

private theorem stage_locallyClosed {rT : Type} :
    (.lam (.lam stageBody) : Exp rT).IsLocallyClosed := by
  rw [← binomialStage_eq]
  exact ClosedExp.lc

private theorem opened_coin_locallyClosed {rT : Type} (coin : Val rT) :
    (Exp.lam (Exp.openRec 1 coin.fst stageBody) : Exp rT).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 0 (Exp.open' (.lam stageBody) coin.fst) = true
  apply Exp.lcb_openRec (Exp.lc_imp_lcb coin.lc)
  change Exp.lcb 0 (.lam (.lam (stageBody : Exp rT))) = true
  exact Exp.lc_imp_lcb stage_locallyClosed

theorem opened_stage {rT : Type} (coin : Val rT) (m : ℕ) :
    Exp.open' (Exp.openRec 1 coin.fst stageBody) (Val.int (m : ℤ)).fst =
      binomialBody coin m := by
  simp [stageBody, binomialBody, bodyCode, Exp.open', Exp.openRec, openRec_val_fst,
    ClosedExp.openRec]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_acceptance (E : CoPset) (m j : ℕ)
    (hlo : m ≤ j) (hhi : j ≤ m + padding m) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (acceptanceBias m j) F) -∗
      tglWp E pl(&Occil.rationalCoin
        #int ((4 : ℤ) ^ m * ((padding m).choose (j - m) : ℤ))
        #int (2 * ((2 * m + padding m).choose j : ℤ)))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have ht := RationalCoin.twp_rationalCoin (rT := rT) (GF := GF) E
    ((4 ^ m * (padding m).choose (j - m) : ℕ) : ℤ)
    ((2 * (2 * m + padding m).choose j : ℕ) : ℤ)
    (by positivity) (by exact_mod_cast denominator_pos m j hhi)
    (by exact_mod_cast numerator_le m j hlo hhi) F
  simpa only [acceptance_eq_ratio m j hlo hhi,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using ht

/-- Binomial sampling cancels the acceptance denominator for every continuation credit. -/
theorem twp_binomialBody (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (m : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (conditionalBias p m) F) -∗
      tglWp E (binomialBody coin m)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  rw [padding_cast]
  iterate 4 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&Occil.binomial &coin.fst #int (2 * (m : ℤ) + padding m))
  isimp only [← binomial_expectation p m F] at Hcredit
  have hs := Binomial.binomial_distSpec E p coin hcoin (2 * m + padding m)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs
  iapply (hs.wp (fun j => RealCoin.credit (acceptanceBias m j) F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %j Hcredit
  iterate 5 twp_pure
  rw [outside_test]
  by_cases hband : m ≤ j ∧ j ≤ m + padding m
  · rw [decide_eq_false (not_not.mpr hband)]
    twp_pure
    twp_bind pl(&Occil.FactoryExtra.choose #int (padding m : ℤ) (#int (j : ℤ) - #int (m : ℤ)))
    twp_pure
    rw [show (j : ℤ) - m = ((j - m : ℕ) : ℤ) by omega]
    iapply tglWp_wand
    isplitl []
    · iapply FactoryChoose.twp_choose E (padding m) (j - m)
    iintro %v %hv
    subst v
    twp_bind pl(&Occil.FactoryExtra.intPower #4 #int (m : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply FactoryIntegerPower.twp_intPower E 4 m
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    simp only [ClosedExp.openRec]
    twp_bind pl(&Occil.FactoryExtra.choose #int (2 * (m : ℤ) + padding m) #int (j : ℤ))
    iapply tglWp_wand
    isplitl []
    · have ht := FactoryChoose.twp_choose (rT := rT) (GF := GF) E (2 * m + padding m) j
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at ht
      iapply ht
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    simp only [ClosedExp.openRec]
    iapply twp_acceptance E m j hband.1 hband.2 F $$ Hcredit
  · rw [decide_eq_true hband]
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [acceptance_eq_zero m j hband, RealCoin.credit_zero] at Hcredit
    iframe Hcredit
    itrivial

/-- The closed two-argument stage, convenient for independent callers. -/
theorem twp_binomialStage (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (m : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (conditionalBias p m) F) -∗
      tglWp E pl(&binomialStage &coin.fst #int (m : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  rw [binomialStage_eq]
  iintro Hcredit
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL (Val.int (m : ℤ))]
      (.app (.lam (.lam stageBody)) coin.fst)) _)
  iapply (twp_beta E [.appL (Val.int (m : ℤ))] (.lam stageBody) coin
    stage_locallyClosed _)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (Exp.openRec 1 coin.fst stageBody)) (Val.int (m : ℤ)).fst)) _)
  iapply (twp_beta E [] (Exp.openRec 1 coin.fst stageBody) (Val.int (m : ℤ))
    (opened_coin_locallyClosed coin) _)
  ieval (
    change _ ⊢ tglWp E
      (Exp.open' (Exp.openRec 1 coin.fst stageBody) (Val.int (m : ℤ)).fst) _)
  rw [opened_stage]
  iapply twp_binomialBody E p coin hcoin m F $$ Hcredit

end specification

end

end SampLib.MinimumComplement
