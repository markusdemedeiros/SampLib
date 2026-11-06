import SampLib.Samplers.PiConstants
import SampLib.Samplers.PLogInverse
import SampLib.Syntax.ClosedExp

/-! # The logarithmic π coin

The local loop counts failures of the reciprocal-π coin. Mixing the reciprocal
positive counts evaluates the logarithmic series, using the general `PLogInverse` identity.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LogPiOverPi

noncomputable section

private theorem inverse_pos : 0 < (PiConstants.inverseBias : ℝ) := by
  rw [PiConstants.inverseBias_coe]
  positivity

def bias : unitInterval := PLogInverse.bias PiConstants.inverseBias inverse_pos

theorem bias_coe : (bias : ℝ) = Real.log Real.pi / Real.pi := by
  simp only [bias, PLogInverse.bias, Subtype.coe_mk, PiConstants.inverseBias_coe, one_div_one_div]
  ring

private theorem count_credit_zero (F : Bool → ℝ≥0∞) :
    RealCoin.credit (PLogInverse.countBias 0) F = F false := by
  simp [PLogInverse.countBias, RealCoin.credit, RealCoin.pmf]

/-- Normalized standalone recursion; `source_eq` checks its occurrence in the sampler. -/
@[pl_fold] private def count {rT : Type} (coin : Val rT) : Exp rT :=
  .fix (.lam (.cond (.app coin.fst (.lit .unit)) (.bvar 0)
    (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))))

private instance inversePi_closed {rT : Type} :
    ClosedExp (Occil.Constants.inversePi : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.Constants.inversePi, Occil.Constants.reciprocalPiScaled,
      Occil.Constants.piBounds, Occil.Constants.arctanReciprocalBounds,
      Occil.Constants.fromBounds, Occil.newUniformBag, Exp.fv,
      UniformBag.uniformBagLess_fv]

private def inverseCoin {rT : Type} : Val rT :=
  ⟨Occil.Constants.inversePi, by unfold Occil.Constants.inversePi; exact .lam (by is_lc),
    ClosedExp.lc⟩

private instance inverseCoin_closed {rT : Type} :
    ClosedExp (inverseCoin : Val rT).fst := inversePi_closed

private instance count_closed {rT : Type} (coin : Val rT) [ClosedExp coin.fst] :
    ClosedExp (count coin) where
  lc := by unfold count; is_lc
  fv := by simp [count, Exp.fv, ClosedExp.fv]

private theorem count_openRec {rT : Type} (coin : Val rT) (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (count coin) = count coin :=
  (Exp.open_lc k e _ (by unfold count; is_lc)).symm

private theorem source_eq {rT : Type} :
    (Occil.Constants.logPiOverPi : Exp rT) = pl(fun u,
      let failures := &(count inverseCoin);
      let n := failures #0;
      if n = #0 then #false else &Occil.rationalCoin #1 n) := by
  kernel_rfl

private theorem one_lt_factor (p : unitInterval) (hp : 0 < (p : ℝ)) :
    1 < Geometric.terminationFactor p := by
  change 1 < 1 + unitInterval.toNNReal p
  exact lt_add_of_pos_right _ (by exact_mod_cast hp)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec count_openRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_count (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT) [ClosedExp coin.fst]
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (offset : ℤ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (Geometric.credit p F) -∗
      tglWp E pl(&(count coin) #int offset)
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (offset + n)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert! %offset %F
  iapply ErrorCredit.Induction.simple hε (one_lt_factor p hp) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %offset %F Hcredit
  iterate 2 twp_pure
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Hcredit
  isimp only [← Geometric.lintegral_coinCredit p hp F ε]
    at Hcredit
  iapply (hcoin.wp
    (Geometric.coinCredit p F ε) (measurable_of_countable _) _)
    $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [Geometric.coinCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_pure
    twp_bind pl(&(count coin) #int (offset + 1))
    iapply tglWp_wand
    isplitl [IH Hcredit Hterm]
    · iapply IH $$ Hterm %(offset + 1) %(fun n => F (n + 1)) Hcredit
    iintro %v ⟨%n, %hv, Hcredit⟩
    subst v
    twp_value
    imodintro
    iexists n + 1
    iframe Hcredit
    ipureintro
    rw [Nat.cast_add_one, add_right_comm offset (1 : ℤ) (n : ℤ), add_assoc]
    rfl
  · isimp only [Geometric.coinCredit] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_value
    imodintro
    iexists 0
    iframe Hcredit
    ipureintro
    simp

/-- Draw the local geometric count, then its reciprocal-count coin. -/
theorem twp_logPiOverPi (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit bias F) -∗
      tglWp E pl(&Occil.Constants.logPiOverPi #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  rw [source_eq]
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(&(count inverseCoin) #0)
  isimp only [bias,
    ← PLogInverse.expectation_preservation PiConstants.inverseBias inverse_pos F] at Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · have hcount := twp_count (rT := rT) (GF := GF) E PiConstants.inverseBias inverse_pos
        inverseCoin (PiConstants.inversePi_distSpec E) 0
        (fun n => RealCoin.credit (PLogInverse.countBias n) F)
    unfold Geometric.credit at hcount
    iapply hcount $$ Hcredit
  iintro %v ⟨%n, %hv, Hcredit⟩
  subst v
  cases n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [count_credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n =>
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, Int.zero_add]
    isimp only [PLogInverse.countBias] at Hcredit
    iapply (RationalCoin.twp_rationalCoin E 1 (n + 1) _ _ _ F) $$ Hcredit

/-- The concrete loop samples the logarithmic probability `log π / π`. -/
theorem logPiOverPi_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.logPiOverPi #())
      (RealCoin.law bias) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails (twp_logPiOverPi E F)

end specification

end

end SampLib.LogPiOverPi
