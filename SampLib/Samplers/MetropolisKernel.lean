import SampLib.Distributions.MetropolisRatio
import SampLib.SupportedSpec
import SampLib.ProofMode.BindFrom
import Samplers.General.Core

/-! # Program logic for rational acceptance ratios

Fresh proposal calls carry their conditional law. Deterministic callbacks supply
integer target weights and rational acceptance ratios. Exact Hastings and
symmetric Metropolis instantiate the same symbolic execution.
-/

open ProbLang
open scoped ENNReal NNReal

set_option maxHeartbeats 200000

namespace SampLib.MetropolisRatio

noncomputable section

private theorem positive_test (a : ℕ) (ha : 0 < a) :
    decide ((a : ℤ) ≤ 0) = false := by simp [Nat.ne_of_gt ha]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
local bi (IProp GF)

attribute [local pl_step_simp] RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec

/-- Deterministic weight/probability callbacks and fresh proposal calls implement the kernel. -/
theorem twp_kernel (E : CoPset) (w : α → ℕ) (r : Ratios α) (μ : α → MeasureTheory.Measure α)
    [∀ x, MeasureTheory.IsProbabilityMeasure (μ x)]
    (hsupport : ∀ x, ∀ᵐ y ∂μ x, 0 < r.numerator x y)
    (encode : α → Val rT) (target proposal q : Val rT)
    (htarget : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hq : ∀ x y, ⊢ tglWp E pl(&q.fst &(encode x).fst &(encode y).fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int (r.numerator x y))
        (Val.int (r.denominator x y))⌝)))
    (hproposal : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst)
      (μ x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) (F : α → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law w r μ n x) -∗
      tglWp E pl(&Occil.General.metropolisHastings &target.fst &proposal.fst &q.fst
        &(encode x).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z))) := by
  induction n generalizing x F with
  | zero =>
    isimp [Occil.General.metropolisHastings, Exp.close, Exp.closeRec]
    iintro Hcredit
    iterate 10 twp_pure
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (encode x)))
    iexists x
    isimp only [law, FiniteKernels.iterate, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    isimp [Occil.General.metropolisHastings, Exp.close, Exp.closeRec]
    iintro Hcredit
    iterate 10 twp_pure
    twp_bind pl(&proposal.fst &(encode x).fst)
    isimp only [← expectation] at Hcredit
    iapply ((hproposal x).wp_supported (fun y => 0 < r.numerator x y)
      (Set.to_countable _).measurableSet (hsupport x)
      (fun y => RealCoin.credit (Metropolis.bias (fun z => (w z : ℝ≥0))
        (weight r) x y)
        (fun b => ∫⁻ z, F z ∂law w r μ n (if b then y else x)))
      (measurable_of_countable _) _) $$ Hcredit
    iintro %y %hy Hcredit
    twp_pures
    twp_bind pl(&q.fst &(encode x).fst &(encode y).fst)
    iapply tglWp_wand
    isplitl []
    · iapply hq x y
    iintro %v %hv
    subst v
    twp_pures
    twp_bind pl(&q.fst &(encode y).fst &(encode x).fst)
    iapply tglWp_wand
    isplitl []
    · iapply hq y x
    iintro %v %hv
    subst v
    twp_pures
    twp_bind pl(&target.fst &(encode y).fst)
    iapply tglWp_wand
    isplitl []
    · iapply htarget y
    iintro %v %hv
    subst v
    twp_pures
    twp_bind pl(&target.fst &(encode x).fst)
    iapply tglWp_wand
    isplitl []
    · iapply htarget x
    iintro %v %hv
    subst v
    twp_pures
    simp only [← Nat.cast_mul]
    rw [positive_test (w x * r.numerator x y * r.denominator y x)
      (denominator_pos w r x y hx hy), Bool.false_or]
    twp_pure
    have hcoin := CappedRationalCoin.distSpec (GF := GF) E
      (numerator w r x y) (denominator w r x y) (by positivity)
      (by exact_mod_cast denominator_pos w r x y hx hy)
    rw [← bias_eq w r x y hx hy] at hcoin
    have hbind := hcoin.spec
      (fun b => ∫⁻ z, F z ∂law w r μ n (if b then y else x))
      (measurable_of_countable _)
    twp_bind_from hbind
    isimp only [← RealCoin.lintegral_law] at Hcredit
    iapply (hcoin.wp_supported (fun b => b = true → 0 < w y)
      (Set.to_countable _).measurableSet (accept_support w r x y)
      (fun b => ∫⁻ z, F z ∂law w r μ n (if b then y else x))
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b %hb Hcredit
    cases b with
    | false =>
      iterate 4 twp_pure
      rw [add_sub_cancel_right]
      have hrec := ih x hx F
      simp [Occil.General.metropolisHastings, Exp.close, Exp.closeRec] at hrec
      exact wand_entails hrec
    | true =>
      iterate 4 twp_pure
      rw [add_sub_cancel_right]
      have hrec := ih y (hb rfl) F
      simp [Occil.General.metropolisHastings, Exp.close, Exp.closeRec] at hrec
      exact wand_entails hrec

/-- Finite iteration of the proposal-and-acceptance kernel. -/
theorem kernel_distSpec (E : CoPset) (w : α → ℕ) (r : Ratios α) (μ : α → MeasureTheory.Measure α)
    [∀ x, MeasureTheory.IsProbabilityMeasure (μ x)]
    (hsupport : ∀ x, ∀ᵐ y ∂μ x, 0 < r.numerator x y)
    (encode : α → Val rT) (target proposal q : Val rT)
    (htarget : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hq : ∀ x y, ⊢ tglWp E pl(&q.fst &(encode x).fst &(encode y).fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int (r.numerator x y))
        (Val.int (r.denominator x y))⌝)))
    (hproposal : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst)
      (μ x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) :
    IsDistSpec (GF := GF) E pl(&Occil.General.metropolisHastings &target.fst &proposal.fst
      &q.fst &(encode x).fst #int (n : ℤ)) (law w r μ n x) encode where
  spec F _ := wand_entails
    (twp_kernel E w r μ hsupport encode target proposal q htarget hq hproposal n x hx F)

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero transitions do not invoke any callback or inspect the initial value. -/
theorem zero_distSpec (E : CoPset)
    (target proposal q initial : Val rT) :
    IsDistSpec (GF := GF) E pl(&Occil.General.metropolisHastings &target.fst &proposal.fst
      &q.fst &initial.fst #0) (MeasureTheory.Measure.dirac ()) (fun _ : Unit => initial) where
  spec F _ := by
    isimp [Occil.General.metropolisHastings, Exp.close, Exp.closeRec]
    iintro Hcredit
    iterate 10 twp_pure
    iapply (tglWp_value_of_toVal (Val.toVal?_fst initial))
    iexists ()
    iframe Hcredit
    itrivial

end specification

end

end SampLib.MetropolisRatio
