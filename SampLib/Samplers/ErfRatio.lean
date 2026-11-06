import SampLib.SquaredDecreasingChain
import SampLib.Distributions.ErrorFunctionKernel
import SampLib.Distributions.ThresholdRejection
import Samplers.Constants.Special

/-! # Error-function ratios from a maximum-uniform decreasing chain

A proposal `t` is retained with probability `exp(-t²)`. Conditioning a uniform
proposal on that event gives the normalized Gaussian integral below the threshold.
-/

open ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.ErfRatio

noncomputable section

section mathematics

open Set MeasureTheory

private theorem mass_ne_zero : AcceptedProposal.mass unifUnit SquaredDecreasing.decay ≠ 0 :=
  ThresholdRejection.mass_ne_zero _ _ SquaredDecreasing.measurable_decay
    (fun _ => Real.exp_pos _)

def bias (x : ℝ) : unitInterval :=
  ThresholdRejection.bias unifUnit SquaredDecreasing.decay mass_ne_zero x

/-- The usual error-function normalization, including thresholds zero and one. -/
theorem bias_coe (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (bias x : ℝ) = ErrorFunctionKernel.erf x / ErrorFunctionKernel.erf 1 := by
  rw [bias, ThresholdRejection.bias_coe, ErrorFunctionKernel.window_mass x hx,
    ErrorFunctionKernel.mass_eq,
    ENNReal.toReal_ofReal (ErrorFunctionKernel.integral_nonneg x hx.1),
    ENNReal.toReal_ofReal (ErrorFunctionKernel.integral_nonneg 1 zero_le_one),
    ErrorFunctionKernel.ratio_eq]

def drawCredit (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  ThresholdRejection.kernel unifUnit SquaredDecreasing.decay mass_ne_zero x F ε

def branchCredit (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (bias x) F + AcceptedProposal.factor unifUnit SquaredDecreasing.decay * ε

private theorem chain_credit (x t : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    SquaredDecreasingChain.credit (F (ThresholdRejection.event x t)) (branchCredit x F ε) 0 t =
      drawCredit x F ε t := by
  simp only [SquaredDecreasingChain.credit, SquaredDecreasingChain.terminal,
    Nat.zero_mod, Nat.zero_add, Nat.mod_succ, ite_true, Nat.one_ne_zero, ite_false,
    RealCoin.credit, RealCoin.pmf, Bool.false_eq_true, branchCredit, drawCredit,
    ThresholdRejection.kernel, AcceptedProposal.kernel, AcceptedProposal.weight,
    AcceptedProposal.rejectedWeight, AcceptedProposal.credit, ThresholdRejection.credit_eq,
    bias]

theorem expectation_preservation (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ t, drawCredit x F ε t ∂unifUnit ≤ RealCoin.credit (bias x) F + ε :=
  ThresholdRejection.expectation_preservation _ _ SquaredDecreasing.measurable_decay
    mass_ne_zero x F ε

end mathematics

@[pl_fold] private def loop : Exp ℝ := pl%
  rec draw x u :=
    let value := urand;
    let chain := &SquaredDecreasingChain.chain;
    let count := chain value #0;
    if count % #2 = #0 then value < x else draw x #()

private theorem source_eq : (Occil.Constants.erfRatio : Exp ℝ) = loop := by kernel_rfl

private theorem natCast_emod_two (k : ℕ) : (k : ℤ) % 2 = ((k % 2 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

private theorem twp_loop (E : CoPset) (x : ℝ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias x) F) -∗ tglWp E pl(&loop #real x #())
      (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor unifUnit SquaredDecreasing.decay mass_ne_zero) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(urand)
  icombine Hcredit Hterm as Hcredit
  iapply (twp_urand_exp (ε₂ := drawCredit x F ε)
    (ThresholdRejection.measurable_kernel _ _ SquaredDecreasing.measurable_decay
      mass_ne_zero x F ε) (expectation_preservation x F ε)) $$ Hcredit
  iintro %t ⟨%ht, Hcredit⟩
  have ht' := mem_unifUnitSupport_real.mp ht
  iterate 2 twp_pure
  twp_bind pl(&SquaredDecreasingChain.chain #real t #0)
  isimp only [← chain_credit x t F ε] at Hcredit
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗
    ↯ (SquaredDecreasingChain.terminal
      (F (ThresholdRejection.event x t)) (branchCredit x F ε) k))))
  isplitl [Hcredit]
  · iapply (SquaredDecreasingChain.twp_chain E _ _ ⟨t, ht'.1.le, ht'.2.le⟩ ht' 0 t
      ⟨ht'.1.le, le_rfl⟩) $$ Hcredit
  iintro %v ⟨%k, %hv, Hcredit⟩
  subst v
  twp_pures
  obtain hk | hk := Nat.mod_two_eq_zero_or_one k
  · rw [natCast_emod_two, hk]
    twp_pures
    twp_value
    imodintro
    iexists ThresholdRejection.event x t
    isimp only [SquaredDecreasingChain.terminal, hk, ite_true] at Hcredit
    iframe Hcredit
    ipureintro
    exact congrArg Val.bool (ThresholdRejection.event_eq_decide x t).symm
  · rw [natCast_emod_two, hk]
    isimp only [SquaredDecreasingChain.terminal, hk, Nat.one_ne_zero, ite_false,
      branchCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&loop #real x #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit

/-- Exact-real correctness of Occil's maximum-chain implementation. -/
theorem erfRatio_distSpec (E : CoPset) (x : unitInterval) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.erfRatio #real (x : ℝ) #())
      (RealCoin.law (bias x)) Val.bool where
  spec F _ := by
    simpa only [source_eq, RealCoin.lintegral_law] using wand_entails (twp_loop E x F)

end specification

end

end SampLib.ErfRatio
