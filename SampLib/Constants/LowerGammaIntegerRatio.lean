import Metrology.Iris.LocalBI
import SampLib.Core.SupportedSpec
import SampLib.Constants.Support.OrderStatisticMaximum
import SampLib.Common.DecreasingTrial
import SampLib.Constants.Laws.ThresholdRejection
import SampLib.Constants.Laws.IntegerGammaKernel
import SampLib.Core.Syntax.ClosedExp
import Samplers.Constants.Special

/-! # The integer-shape lower incomplete-gamma ratio

The maximum of `m` uniforms proposes density `m t^(m-1)`. Even parity
of the decreasing chain accepts with probability `exp(-t)`, leaving the
normalized incomplete-gamma density on the unit interval.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.LowerGammaIntegerRatio

noncomputable section

section mathematics

open Set MeasureTheory

abbrev acceptance := ExponentialFactory.decay (1 : unitInterval)

private theorem mass_ne_zero (n : ℕ) :
    AcceptedProposal.mass (MaximumUniform.law n) acceptance ≠ 0 :=
  ThresholdRejection.mass_ne_zero _ _ (ExponentialFactory.measurable_decay 1)
    (fun _ => Real.exp_pos _)

/-- The regularized threshold under density `t^n exp(-t)` on `[0,1]`. -/
def bias (n : ℕ) (x : ℝ) : unitInterval :=
  ThresholdRejection.bias (MaximumUniform.law n) acceptance (mass_ne_zero n) x

/-- The classical lower incomplete-gamma ratio; the proposal's factor cancels. -/
theorem bias_coe (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (bias n x : ℝ) = IntegerGammaKernel.lowerGamma n x / IntegerGammaKernel.lowerGamma n 1 := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ IntegerGammaKernel.lowerGamma n y :=
    intervalIntegral.integral_nonneg hy
      (fun t ht => mul_nonneg (pow_nonneg ht.1 _) (Real.exp_pos _).le)
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [bias, ThresholdRejection.bias_coe, IntegerGammaKernel.window_mass n x hx,
    IntegerGammaKernel.mass_eq, ENNReal.toReal_ofReal (mul_nonneg hn.le (hnonneg x hx.1)),
    ENNReal.toReal_ofReal (mul_nonneg hn.le (hnonneg 1 zero_le_one)),
    mul_div_mul_left _ _ hn.ne']

def parityCredit (n : ℕ) (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (t : ℝ) (k : ℕ) : ℝ≥0∞ :=
  if k % 2 = 0 then F (ThresholdRejection.event x t) else
    RealCoin.credit (bias n x) F + AcceptedProposal.factor (MaximumUniform.law n) acceptance * ε

def drawCredit (n : ℕ) (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ThresholdRejection.kernel (MaximumUniform.law n) acceptance (mass_ne_zero n) x F ε t

private theorem parity_expectation (n : ℕ) (x : ℝ) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    DecreasingTrial.credit (parityCredit n x F ε t) 0 t = drawCredit n x F ε t := by
  change DecreasingTrial.credit (fun k => if k % 2 = 0 then _ else _) 0 t = _
  dsimp only [DecreasingTrial.credit]
  rw [TotalEris.Examples.RealDecrTrialCreditV_parity
    (F (ThresholdRejection.event x t))
    (RealCoin.credit (bias n x) F + AcceptedProposal.factor (MaximumUniform.law n) acceptance * ε)
    ht.1 ht.2]
  simp only [drawCredit, ThresholdRejection.kernel, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight,
    AcceptedProposal.credit, ThresholdRejection.credit_eq, bias,
    acceptance, ExponentialFactory.decay_coe _ _ ht.1, Set.Icc.coe_one, one_mul, neg_mul]

/-- Proposal weighting preserves the threshold credit and funds every retry. -/
theorem expectation_preservation (n : ℕ) (x : ℝ) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ t, drawCredit n x F ε t ∂MaximumUniform.law n ≤ RealCoin.credit (bias n x) F + ε :=
  ThresholdRejection.expectation_preservation _ _ (ExponentialFactory.measurable_decay 1)
    (mass_ne_zero n) x F ε

end mathematics

private instance orderStatistic_closed : ClosedExp (Occil.orderStatistic : Exp ℝ) where
  lc := by is_lc
  fv := by simp [Occil.orderStatistic, Occil.getAt, Occil.insertReal, Exp.fv]

private instance decreasingTrial_closed : ClosedExp (Occil.decreasingTrial : Exp ℝ) where
  lc := DecreasingTrial.decreasingTrial_lc
  fv := DecreasingTrial.decreasingTrial_fv

private theorem natCast_emod_two (k : ℕ) : (k : ℤ) % 2 = ((k % 2 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

theorem twp_lowerGammaIntegerRatio (E : CoPset) (n : ℕ) (x : ℝ)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias n x) F) -∗
      tglWp E pl(&Occil.Constants.lowerGammaIntegerRatio #int ((n + 1 : ℕ) : ℤ) #real x #())
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor (MaximumUniform.law n) acceptance (mass_ne_zero n))
    $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 6 twp_pure
  twp_bind pl(&Occil.orderStatistic #int ((n + 1 : ℕ) : ℤ) #int ((n + 1 : ℕ) : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation_preservation n x F ε) $$ Hcredit
  iapply ((OrderStatisticMaximum.orderStatistic_max_distSpec E n).wp_supported
    (fun t => t ∈ Set.Icc (0 : ℝ) 1) measurableSet_Icc (MaximumUniform.ae_mem_unit n)
    (drawCredit n x F ε)
    (ThresholdRejection.measurable_kernel _ _ (ExponentialFactory.measurable_decay 1)
      (mass_ne_zero n) x F ε) _) $$ Hcredit
  iintro %t %ht Hcredit
  twp_pure
  twp_bind pl(&Occil.decreasingTrial #0 #real t)
  isimp only [← parity_expectation n x F ε t ht] at Hcredit
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ k : ℕ,
    ⌜v = Val.int k⌝ ∗ ↯ (parityCredit n x F ε t k))))
  isplitl [Hcredit]
  · iapply (DecreasingTrial.twp_decreasingTrial E _ 0 t ht) $$ Hcredit
  iintro %v ⟨%k, %hv, Hcredit⟩
  subst v
  twp_pures
  obtain hk | hk := Nat.mod_two_eq_zero_or_one k
  · rw [natCast_emod_two, hk]
    twp_pures
    twp_value
    imodintro
    iexists ThresholdRejection.event x t
    isimp only [parityCredit, hk, ite_true] at Hcredit
    iframe Hcredit
    ipureintro
    exact congrArg Val.bool (ThresholdRejection.event_eq_decide x t).symm
  · rw [natCast_emod_two, hk]
    isimp only [parityCredit, hk, Nat.one_ne_zero, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&Occil.Constants.lowerGammaIntegerRatio
      #int ((n + 1 : ℕ) : ℤ) #real x #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit

/-- Every positive integer shape and every unit-interval threshold, with ENNReal credits. -/
theorem lowerGammaIntegerRatio_distSpec (E : CoPset) (m : ℕ) (hm : 0 < m)
    (x : unitInterval) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.lowerGammaIntegerRatio #int (m : ℤ) #real (x : ℝ) #())
      (RealCoin.law (bias (m - 1) x)) Val.bool where
  spec F _ := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right, RealCoin.lintegral_law] using
      wand_entails (twp_lowerGammaIntegerRatio E n x F)

end specification

end

end SampLib.LowerGammaIntegerRatio
