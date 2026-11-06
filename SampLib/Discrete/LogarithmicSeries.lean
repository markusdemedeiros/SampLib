import SampLib.Discrete.Laws.LogarithmicSeries
import SampLib.Discrete.Laws.BinomialBinary
import SampLib.Core.Syntax.ClosedExp
import Samplers.Discrete.Counts
import Metrology.Iris.LocalBI

/-! # Logarithmic-series sampling by reciprocal rejection

A geometric count is accepted with probability the reciprocal of its positive
successor. The accepted-proposal identity preserves arbitrary continuation
credits and pays for the single retry amplification.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.LogarithmicSeries

noncomputable section

private theorem bias_pos (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    0 < (BinomialBinary.bias a b : ℝ) := by
  rw [BinomialBinary.bias_coe a b (by omega) hab.le]
  exact div_pos (by exact_mod_cast ha) (by exact_mod_cast lt_trans ha hab)

private theorem bias_lt_one (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    (BinomialBinary.bias a b : ℝ) < 1 := by
  rw [BinomialBinary.bias_coe a b (by omega) hab.le]
  exact (div_lt_one (by exact_mod_cast lt_trans ha hab)).mpr (by exact_mod_cast hab)

/-- The standard logarithmic-series law at a valid rational parameter. -/
abbrev rationalLaw (a b : ℕ) (ha : 0 < a) (hab : a < b) :=
  law (BinomialBinary.bias a b) (bias_pos a b ha hab) (bias_lt_one a b ha hab)

section mathematics

open MeasureTheory

/-- Accept the positive successor or retain the amplified retry budget. -/
def branchCredit (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ) (accepted : Bool) : ℝ≥0∞ :=
  if accepted then F (n + 1) else
    (∫⁻ k, F k ∂law p hp hp1) + AcceptedProposal.factor (proposal p) acceptance * ε

/-- Conditional expectation of the reciprocal acceptance coin. -/
def proposalCredit (p : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  RealCoin.credit (acceptance n) (branchCredit p hp hp1 F ε n)

/-- Reciprocal weighting preserves the logarithmic-series expectation and retry slack. -/
theorem expectation_preservation (p : unitInterval) (hp : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ n, proposalCredit p hp hp1 F ε n ∂proposal p) ≤
      (∫⁻ k, F k ∂law p hp hp1) + ε := by
  have hC : AcceptedProposal.credit (proposal p) acceptance (mass_pos p hp hp1)
      (fun n => F (n + 1)) = ∫⁻ k, F k ∂law p hp hp1 := expectation p hp hp1 F
  simpa only [proposalCredit, branchCredit, RealCoin.credit, RealCoin.pmf,
    ite_true, Bool.false_eq_true, ite_false, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, hC] using
    AcceptedProposal.expectation_preservation (proposal p) acceptance
      (measurable_of_countable _) (mass_pos p hp hp1) (fun n => F (n + 1))
      (measurable_of_countable _) ε

private theorem proposal_bias (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    RationalCoin.bias (b - a : ℕ) b (by omega) (by omega) (by omega) =
      unitInterval.symm (BinomialBinary.bias a b) := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, BinomialBinary.bias_coe a b (by omega) hab.le]
  simp only [RationalCoin.bias, Int.cast_natCast, Nat.cast_sub hab.le]
  push_cast
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (lt_trans ha hab).ne'
  field_simp

end mathematics

private def proposalCoin {rT : Type _} (a b : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin (#int (b : ℤ) - #int (a : ℤ)) #int (b : ℤ)),
    .lam (by is_lc), by is_lc⟩

private instance rational_closed {rT : Type _} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := RationalCoin.rationalCoin_fv

private instance geometric_closed {rT : Type _} : ClosedExp (Occil.geometric : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.geometric, Exp.fv]

private instance proposal_closed {rT : Type _} (a b : ℕ) :
    ClosedExp ((proposalCoin a b : Val rT).fst) where
  lc := by is_lc
  fv := by simp [proposalCoin, Exp.fv, RationalCoin.rationalCoin_fv]

private def loop {rT : Type _} (a b : ℕ) : Exp rT := pl%
  rec draw u :=
    let n := #1 + &Occil.geometric &(proposalCoin a b).fst #();
    if &Occil.rationalCoin #1 n then n else draw #()

private theorem valid_test (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    Bool.or (decide ((a : ℤ) ≤ 0)) (decide ((b : ℤ) ≤ a)) = false := by
  simp [Nat.ne_of_gt ha, show ¬(b : ℤ) ≤ a by omega]

private theorem sub_cast (a b : ℕ) (hab : a ≤ b) :
    (b : ℤ) - a = ((b - a : ℕ) : ℤ) := (Nat.cast_sub hab).symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem proposal_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    IsDistSpec (GF := GF) E pl(&(proposalCoin a b).fst #())
      (RealCoin.law (unitInterval.symm (BinomialBinary.bias a b))) Val.bool where
  spec F hF := by
    have h := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E (b - a : ℕ) b (by omega) (by omega) (by omega)
    rw [proposal_bias a b ha hab] at h
    iintro Hcredit
    iterate 2 twp_pure
    rw [sub_cast a b hab.le]
    simp only [ClosedExp.openRec, Exp.ofVal]
    iapply h.spec F hF $$ Hcredit

private theorem acceptance_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #1 #int ((n + 1 : ℕ) : ℤ))
      (RealCoin.law (acceptance n)) Val.bool := by
  simpa only [acceptance, PLogInverse.countBias, Nat.cast_add, Nat.cast_one] using
    RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
      E 1 (n + 1) (by omega) (by omega) (by omega)

private theorem twp_loop (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ n, F n ∂rationalLaw a b ha hab) -∗ tglWp E pl(&(loop a b) #())
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  let p := BinomialBinary.bias a b
  have hp := bias_pos a b ha hab
  have hp1 := bias_lt_one a b ha hab
  have hgeom := Geometric.geometric_distSpec (rT := rT) (GF := GF) E
    (unitInterval.symm p) (by simpa [unitInterval.coe_symm_eq] using sub_pos.mpr hp1)
    (proposalCoin a b) (proposal_distSpec E a b ha hab)
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor (proposal p) acceptance (mass_pos p hp hp1)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.geometric &(proposalCoin a b).fst #())
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation_preservation p hp hp1 F ε) $$ Hcredit
  iapply (hgeom.wp (proposalCredit p hp hp1 F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 2 twp_pure
  rw [add_comm (1 : ℤ), ← Nat.cast_add_one]
  twp_bind pl(&Occil.rationalCoin #1 #int ((n + 1 : ℕ) : ℤ))
  isimp only [proposalCredit, ← RealCoin.lintegral_law] at Hcredit
  iapply ((acceptance_distSpec E n).wp (branchCredit p hp hp1 F ε n)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %accepted Hcredit
  cases accepted
  · twp_pure
    isimp only [branchCredit, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&(loop a b) #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · twp_pure
    twp_value
    imodintro
    iexists n + 1
    isimp only [branchCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Exact logarithmic-series sampling for every rational parameter strictly between zero and one. -/
theorem twp_logarithmicSeries (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ n, F n ∂rationalLaw a b ha hab) -∗
      tglWp E pl(&Occil.DiscreteExtra.logarithmicSeries #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  twp_pures
  rw [valid_test a b ha hab]
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&(loop a b) #())
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply twp_loop E a b ha hab F $$ Hcredit

/-- Typed standard logarithmic-series law with arbitrary extended-real continuation credits. -/
theorem logarithmicSeries_distSpec (E : CoPset) (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.logarithmicSeries
      #int (a : ℤ) #int (b : ℤ)) (rationalLaw a b ha hab)
      (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := wand_entails (twp_logarithmicSeries E a b ha hab F)

end specification

end

end SampLib.LogarithmicSeries
