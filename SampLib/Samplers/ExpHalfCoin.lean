import SampLib.Samplers.RealCoin
import SampLib.Samplers.DecreasingTrial
import SampLib.Distributions.Gaussian

/-! # A Bernoulli coin with bias `exp (-1/2)`

The decreasing-chain parity integrates over the lower half of the unit interval;
the upper half returns true. The resulting success probability is `exp (-1/2)`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ExpHalfCoin

noncomputable section

open TotalEris.Examples

abbrev bias := γBNE
abbrev law := RealCoin.law bias

/-- The parity kernel has exactly the negative-exponential Bernoulli expectation. -/
theorem expectation (F : Bool → ℝ≥0∞) :
    ∫⁻ x, BNEHalfCredit F x ∂LawfulProbLangℝ.unifUnit = RealCoin.credit bias F := by
  rw [BNEHalfCredit_lintegral]
  simp only [RealCoin.credit, RealCoin.pmf, bias, γBNE, BNEHalfCreditV, BNEHalfPMF,
    Bool.false_eq_true, ite_true, ite_false]
  ring

theorem expHalfCoin_lc {rT : Type _} [ProbLangℝ rT] :
    (Occil.expHalfCoin : Exp rT).IsLocallyClosed := by is_lc

theorem expHalfCoin_fv {rT : Type _} [ProbLangℝ rT] :
    (Occil.expHalfCoin : Exp rT).fv = ∅ := by
  simp [Occil.expHalfCoin, Exp.fv, DecreasingTrial.decreasingTrial_fv]

@[simp] theorem expHalfCoin_openRec {rT : Type _} [ProbLangℝ rT] (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.expHalfCoin = Occil.expHalfCoin :=
  (Exp.open_lc k e _ expHalfCoin_lc).symm

@[simp] theorem expHalfCoin_closeRec {rT : Type _} [ProbLangℝ rT] (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.expHalfCoin : Exp rT) = Occil.expHalfCoin :=
  Exp.closeRec_fresh x _ k (by simp [expHalfCoin_fv])

private theorem parity_beq (n : ℕ) :
    ((BaseLit.int ((n : ℤ) % 2) : BaseLit ℝ) == .int 1) = decide (n % 2 = 1) := by
  change ((n : ℤ) % 2 == 1) = decide (n % 2 = 1)
  rw [beq_eq_decide, decide_eq_decide]
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

theorem twp_expHalfCoin (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit bias F) -∗ tglWp E pl(&Occil.expHalfCoin #())
      (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pure
  twp_bind pl(urand)
  iapply (twp_urand_exp (measurable_bneHalfCredit F) ?_) $$ Hcredit
  · rw [expectation]
  iintro %x ⟨%hx, Hcredit⟩
  have hx' := mem_unifUnitSupport_real_le hx
  twp_pures
  simp only [realOfRat_real, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  simp only [DecreasingTrial.decreasingTrial_openRec, DecreasingTrial.decreasingTrial_closeRec]
  by_cases hhalf : x ≤ 1 / 2
  · rw [show ProbLangℝ.realLe x (1 / 2) = true from decide_eq_true hhalf]
    isimp only [BNEHalfCredit, ite_eq_left hhalf,
      ite_eq_right (not_not_intro hhalf), add_zero] at Hcredit
    twp_pure
    twp_bind pl(&Occil.decreasingTrial #0 #real x)
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (DecreasingTrial.twp_decreasingTrial E (LiftParity F) 0 x hx') $$ Hcredit
    iintro %v ⟨%n, %hv, Hcredit⟩
    subst v
    twp_pures
    rw [parity_beq]
    twp_value
    imodintro
    iexists decide (n % 2 = 1)
    isimp only [LiftParity] at Hcredit
    iframe Hcredit
    itrivial
  · rw [show ProbLangℝ.realLe x (1 / 2) = false from decide_eq_false hhalf]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [BNEHalfCredit, ite_eq_right hhalf, ite_eq_left hhalf, zero_add] at Hcredit
    iframe Hcredit
    itrivial

theorem expHalfCoin_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.expHalfCoin #()) law Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails (twp_expHalfCoin E F)

end specification

end

end SampLib.ExpHalfCoin
