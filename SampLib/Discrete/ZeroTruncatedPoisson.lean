import SampLib.Discrete.PoissonRational
import SampLib.Continuous.Rejection
import Samplers.Discrete.Counts

/-! # A Poisson count conditioned to be positive -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.ZeroTruncatedPoisson

noncomputable section

section mathematics

open MeasureTheory

abbrev acceptance : Set ℕ := Set.Ioi 0

theorem acceptance_mass (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    ProbabilityTheory.poissonMeasure (PoissonRational.rate x y) acceptance ≠ 0 := by
  have hr : (0 : ℝ≥0) < PoissonRational.rate x y := by
    unfold PoissonRational.rate
    positivity
  have hr' : (0 : ℝ) < PoissonRational.rate x y := by exact_mod_cast hr
  have hpoint : 0 < ProbabilityTheory.poissonMeasure (PoissonRational.rate x y) {1} := by
    rw [ProbabilityTheory.poissonMeasure_singleton]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  apply ne_of_gt
  apply lt_of_lt_of_le hpoint
  apply measure_mono
  intro n hn
  simp only [Set.mem_singleton_iff] at hn
  subst n
  decide

def law (x y : ℕ) (hx : 0 < x) (hy : 0 < y) : Measure ℕ :=
  Rejection.law (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance
    (acceptance_mass x y hx hy)

instance (x y : ℕ) (hx : 0 < x) (hy : 0 < y) : IsProbabilityMeasure (law x y hx hy) := by
  unfold law
  infer_instance

abbrev credit (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (F : ℕ → ℝ≥0∞) :=
  Rejection.credit (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance
    (acceptance_mass x y hx hy) F

def kernel (x y : ℕ) (hx : 0 < x) (hy : 0 < y) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :=
  Rejection.kernel (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance
    (acceptance_mass x y hx hy) F ε

private theorem factor_gt_one (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    1 < Rejection.terminationFactor
      (ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) acceptance := by
  exact lt_add_of_pos_right 1
    (ENNReal.toNNReal_pos (acceptance_mass x y hx hy) (measure_ne_top _ _))

/-- Conditioning preserves output credit and pays for amplified zero-count retries. -/
theorem expectation (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ n, kernel x y hx hy F ε n
      ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate x y)) ≤
      credit x y hx hy F + ε :=
  Rejection.expectation_preservation _ acceptance measurableSet_Ioi
    (acceptance_mass x y hx hy) F ε

private theorem positive_test (x : ℕ) (hx : 0 < x) :
    decide ((x : ℤ) ≤ 0) = false := decide_eq_false (by omega)

end mathematics

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_zeroTruncatedPoisson (E : CoPset) (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit x y hx hy F) -∗
      tglWp E pl(&Occil.DiscreteExtra.zeroTruncatedPoisson #int (x : ℤ) #int (y : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (factor_gt_one x y hx hy) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  simp only [positive_test x hx, positive_test y hy, Bool.false_or]
  twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec]
  twp_bind pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation x y hx hy F ε) $$ Hcredit
  iapply ((PoissonRational.poissonRational_distSpec E x y hy).wp
    (kernel x y hx hy F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  twp_pures
  rw [int_beq]
  by_cases hn : n = 0
  · subst n
    rw [Nat.cast_zero, beq_self_eq_true]
    twp_pure
    isimp [kernel, Rejection.kernel] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [Occil.DiscreteExtra.zeroTruncatedPoisson, Exp.close, Exp.closeRec] at IH
    isimp [Exp.ofVal, Exp.close, Exp.closeRec]
    iapply IH $$ Hterm Hcredit
  · rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hn)]
    twp_pures
    twp_value
    imodintro
    iexists n
    isimp [kernel, Rejection.kernel, Nat.pos_iff_ne_zero, hn] at Hcredit
    iframe Hcredit
    itrivial

theorem zeroTruncatedPoisson_distSpec (E : CoPset) (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.zeroTruncatedPoisson #int (x : ℤ) #int (y : ℤ))
      (law x y hx hy) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    simpa only [law, Rejection.credit] using
      wand_entails (twp_zeroTruncatedPoisson E x y hx hy F)

end specification

end

end SampLib.ZeroTruncatedPoisson
