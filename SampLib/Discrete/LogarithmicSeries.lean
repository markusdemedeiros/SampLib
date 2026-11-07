import SampLib.Discrete.Laws.LogarithmicSeries
import SampLib.Discrete.Geometric
import SampLib.Uniform.RationalCoin
import SampLib.Core.Syntax.ClosedExp
import Samplers.Discrete.Counts
import Metrology.Iris.LocalBI
import SampLib.Core.Retry

/-! # Logarithmic-series sampling by reciprocal rejection

A geometric count is accepted with probability the reciprocal of its positive
successor. The accepted-proposal identity preserves arbitrary continuation
credits and pays for the single retry amplification.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.LogarithmicSeries

noncomputable section

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
  iapply Retry.twp_loop solve_not_value
    (AcceptedProposal.one_lt_factor (proposal p) acceptance (mass_pos p hp hp1))
  iintro !> %ε %hε IH Hcredit
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.geometric &(proposalCoin a b).fst #())
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
    twp_bind pl(&(loop a b) #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hcredit
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
