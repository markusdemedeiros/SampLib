import SampLib.Discrete.Laws.ZeroTruncatedPoisson
import SampLib.Discrete.PoissonRational
import SampLib.Continuous.Rejection
import Samplers.Discrete.Counts
import SampLib.Core.Retry

/-! # A Poisson count conditioned to be positive -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.ZeroTruncatedPoisson

noncomputable section

private theorem positive_test (x : ℕ) (hx : 0 < x) :
    decide ((x : ℤ) ≤ 0) = false := decide_eq_false (by omega)

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
  iapply Retry.twp_loop solve_not_value (factor_gt_one x y hx hy)
  iintro !> %ε %hε IH Hcredit
  twp_pures
  simp only [positive_test x hx, positive_test y hy, Bool.false_or]
  twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec]
  twp_bind pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
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
    isimp [Occil.DiscreteExtra.zeroTruncatedPoisson, Exp.close, Exp.closeRec] at IH
    isimp [Exp.ofVal, Exp.close, Exp.closeRec]
    iapply IH $$ Hcredit
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
