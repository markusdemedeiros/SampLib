import SampLib.Constants.Laws.SquaredDecreasing
import SampLib.Common.Laws.BernoulliMixture
import SampLib.Continuous.UniformMax
import SampLib.Core.Syntax.ClosedExp

/-! # Decreasing chains of maximum-uniform proposals

The proposal CDF is `x²`, so retaining the starting parity has probability
`exp(-x²)`. A fixed cap below one supplies the termination amplification.
-/

open ProbLang
open ENNReal (ofReal)
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.SquaredDecreasingChain

noncomputable section

section mathematics

open Set MeasureTheory

open SquaredDecreasing

def terminal (A B : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := if n % 2 = 0 then A else B

def credit (A B : ℝ≥0∞) (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  RealCoin.credit (decay x) (fun a => if a then terminal A B n else terminal A B (n + 1))

def kernel (A B : ℝ≥0∞) (n : ℕ) (x : ℝ) (c : ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if y < x then credit A B (n + 1) y + c else terminal A B n

private theorem terminal_add_two (A B : ℝ≥0∞) (n : ℕ) :
    terminal A B (n + 1 + 1) = terminal A B n := by
  unfold terminal
  rw [show (n + 1 + 1) % 2 = n % 2 by omega]

private theorem kernel_eq (A B : ℝ≥0∞) (n : ℕ) (x : ℝ) (c : ℝ≥0∞) (y : ℝ) :
    kernel A B n x c y =
      RealCoin.credit (flipBias x y)
        (fun a => if a then terminal A B (n + 1) else terminal A B n) +
        (if y < x then 1 else 0) * c := by
  by_cases h : y < x
  · simp only [kernel, flipBias, ite_eq_left h, credit, terminal_add_two, one_mul]
  · simp only [kernel, flipBias, ite_eq_right h, RealCoin.credit, RealCoin.pmf, ite_true,
      Bool.false_eq_true, ite_false, Set.Icc.coe_zero, ENNReal.ofReal_zero, zero_mul,
      sub_zero, ENNReal.ofReal_one, one_mul, zero_add, add_zero]

theorem measurable_kernel (A B : ℝ≥0∞) (n : ℕ) (x : ℝ) (c : ℝ≥0∞) :
    Measurable (kernel A B n x c) := by
  change Measurable (fun y => kernel A B n x c y)
  simp_rw [kernel_eq]
  exact (BernoulliMixture.measurable_credit _ (measurable_flipBias x) _).add
    ((Measurable.ite measurableSet_Iio measurable_const measurable_const).mul_const c)

/-- The parity-reversal mass is `1-exp(-x²)`; continuation consumes mass `x²`. -/
theorem expectation (A B : ℝ≥0∞) (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (c : ℝ≥0∞) :
    ∫⁻ y, kernel A B n x c y ∂MaximumUniform.law 1 = credit A B n x + ofReal (x ^ 2) * c := by
  simp_rw [kernel_eq]
  rw [lintegral_add_left (BernoulliMixture.measurable_credit _ (measurable_flipBias x) _),
    BernoulliMixture.expectation _ (flipBias x) (measurable_flipBias x)
      (unitInterval.symm (decay x))
      (by simpa only [unitInterval.coe_symm_eq] using flip_mass x hx),
    lintegral_mul_const _ (Measurable.ite measurableSet_Iio measurable_const measurable_const),
    continuation_mass x hx]
  congr 1
  simp only [credit, RealCoin.credit, RealCoin.pmf, unitInterval.coe_symm_eq,
    Bool.false_eq_true, ite_true, ite_false, sub_sub_cancel]
  ring

theorem law_eq_maximum : UniformMax.law = MaximumUniform.law 1 := by
  apply Measure.ext_of_Iic
  intro t
  have hs : (fun z : ℝ × ℝ => max z.1 z.2) ⁻¹' Iic t = Iic t ×ˢ Iic t := by
    ext z
    change max z.1 z.2 ≤ t ↔ z.1 ≤ t ∧ z.2 ≤ t
    exact max_le_iff
  rw [UniformMax.law, Measure.map_apply (measurable_fst.max measurable_snd) measurableSet_Iic,
    hs, Measure.prod_prod, MaximumUniform.law_apply_Iic, pow_two]

theorem budget (A B : ℝ≥0∞) (n : ℕ) (cap : unitInterval) (hcap : 0 < (cap : ℝ))
    (x : ℝ) (hx : 0 ≤ x ∧ x ≤ (cap : ℝ)) (ε : ℝ≥0∞) :
    ∫⁻ a, UniformMax.credit (kernel A B n x (ExponentialFactory.factor cap * ε)) a ∂unifUnit ≤
      credit A B n x + ε := by
  rw [UniformMax.expectation_preservation _ (measurable_kernel _ _ _ _ _),
    law_eq_maximum, expectation A B n x ⟨hx.1, hx.2.trans cap.2.2⟩]
  exact add_le_add le_rfl (by
    simpa only [pow_two] using
      ExponentialFactory.amplified_continuation ⟨x, hx.1, hx.2.trans cap.2.2⟩ cap hcap x hx ε)

end mathematics

@[pl_fold] def chain : Exp ℝ := pl%
  rec decrease previous count :=
    let a := urand;
    let b := urand;
    let next := (if a < b then b else a);
    if next < previous then decrease next (count + #1) else count

instance chain_closed : ClosedExp chain where
  lc := by unfold chain; is_lc
  fv := by simp [chain, Exp.fv]

private instance pureExec_maximum [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
    (a b : ℝ) :
    PureExec True 1 pl(if #bool (ProbLangℝ.realLt a b) then #real b else #real a)
      pl(#real (max a b)) := by
  by_cases h : a < b
  · simpa only [ProbLangℝ.realLt, decide_eq_true h, max_eq_right h.le] using
      (inferInstance : PureExec True 1 pl(if #true then #real b else #real a) pl(#real b))
  · simpa only [ProbLangℝ.realLt, decide_eq_false h, max_eq_left (le_of_not_gt h)] using
      (inferInstance : PureExec True 1 pl(if #false then #real b else #real a) pl(#real a))

private theorem natCast_add_one (n : ℕ) : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- A cap below one funds the chain's decreasing continuation probability. -/
theorem twp_chain (E : CoPset) (A B : ℝ≥0∞) (cap : unitInterval)
    (hcap : 0 < (cap : ℝ) ∧ (cap : ℝ) < 1) (n : ℕ) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ (cap : ℝ)) :
    ⊢ ↯ (credit A B n x) -∗ tglWp E pl(&chain #real x #int (n : ℤ))
      (fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (terminal A B k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %n %x %hx Hcredit
  iapply ErrorCredit.Induction.simple hε (ExponentialFactory.one_lt_factor cap hcap) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %n %x %hx Hcredit
  twp_pures
  twp_bind pl(urand)
  icombine Hcredit Hterm as Hcredit
  iapply (twp_urand_exp
    (ε₂ := UniformMax.credit (kernel A B n x (ExponentialFactory.factor cap * ε)))
    (UniformMax.measurable_credit _ (measurable_kernel _ _ _ _ _))
    (budget A B n cap hcap.1 x hx ε)) $$ Hcredit
  iintro %a ⟨%ha, Hcredit⟩
  have ha' := mem_unifUnitSupport_real.mp ha
  twp_pure
  twp_bind pl(urand)
  isimp only [UniformMax.credit] at Hcredit
  iapply (twp_urand_exp
    (ε₂ := fun b => kernel A B n x (ExponentialFactory.factor cap * ε) (max a b))
    ((measurable_kernel _ _ _ _ _).comp (measurable_const.max measurable_id)) le_rfl)
    $$ Hcredit
  iintro %b ⟨%hb, Hcredit⟩
  have hb' := mem_unifUnitSupport_real.mp hb
  twp_pures
  twp_bind pl(if #bool (ProbLangℝ.realLt a b) then #real b else #real a)
  twp_pure_at pl(if #bool (ProbLangℝ.realLt a b) then #real b else #real a) ↦
    pl(#real (max a b)) by trivial
  twp_value
  imodintro
  twp_pures
  rcases hnext : ProbLangℝ.realLt (max a b) x with _ | _
  · isimp only [kernel, of_decide_eq_false hnext, ite_false] at Hcredit
    twp_pures
    twp_value
    imodintro
    iexists n
    iframe Hcredit
    itrivial
  · isimp only [kernel, of_decide_eq_true hnext, ite_true] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    iterate 2 twp_pure
    rw [natCast_add_one]
    twp_bind pl(&chain #real (max a b) #int ((n + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm %(n + 1) %(max a b)
      %⟨(le_max_left a b).trans' ha'.1.le, (of_decide_eq_true hnext).le.trans hx.2⟩ Hcredit

end specification

end

end SampLib.SquaredDecreasingChain
