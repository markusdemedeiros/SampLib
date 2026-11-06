import SampLib.Common.Laws.BooleanEvent
import SampLib.Discrete.Binomial
import SampLib.Common.Syntax.Shuffle
import SampLib.Core.SamplerStep
import Samplers.General.Core

/-! # Exact Monte Carlo permutation-test counts

A replicate is a fresh uniform positional permutation. An exceedance includes a
tie; the returned pair adds the observed arrangement once to both counts.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PermutationTest

noncomputable section

set_option maxHeartbeats 400000

variable {α : Type _}

/-- Ties belong to the exceedance event. -/
def exceeds (xs : List α) (statistic : List α → ℤ)
    (σ : Equiv.Perm (Fin xs.length)) : Bool :=
  decide (statistic xs ≤ statistic (Shuffle.output xs σ))

/-- The exact null exceedance probability, retaining all positional multiplicities. -/
def bias (xs : List α) (statistic : List α → ℤ) : unitInterval :=
  BooleanEvent.bias (Shuffle.law xs) (exceeds xs statistic)

/-- The number of independently sampled null exceedances. -/
abbrev law (xs : List α) (statistic : List α → ℤ) (n : ℕ) :=
  Binomial.law (bias xs statistic) n

/-- The exact numerator and denominator returned by the program. -/
def encode {rT : Type _} (replicates count : ℕ) : Val rT :=
  .pair (.int (count + 1)) (.int (replicates + 1))

section mathematics

open MeasureTheory

/-- Condition on one uniform null permutation, then count the remaining trials. -/
theorem expectation (xs : List α) (statistic : List α → ℤ) (n z : ℕ)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ σ, ∫⁻ k,
        F (if exceeds xs statistic σ then z + 1 + k else z + k)
          ∂law xs statistic n ∂Shuffle.law xs =
      ∫⁻ k, F (z + k) ∂law xs statistic (n + 1) := by
  rw [BooleanEvent.expectation (Shuffle.law xs) (exceeds xs statistic)
    (measurable_of_countable _)
    (fun b => ∫⁻ k, F (if b then z + 1 + k else z + k) ∂law xs statistic n)]
  simpa only [law, Binomial.continuation, bias, add_ite, apply_ite, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using
    Binomial.expectation (bias xs statistic) n (fun k => F (z + k))

end mathematics

private def loop {rT : Type _} [ProbLangℝ rT] (input : α → Val rT)
    (xs : List α) (statistic : Val rT) (observed : ℤ) (replicates : ℕ) : Exp rT :=
  .fix (.lam (.lam (.cond (.binop .eq (.bvar 1) (.lit (.int 0)))
    (.pair (.binop .plus (.bvar 0) (.lit (.int 1)))
      (.binop .plus (.lit (.int replicates)) (.lit (.int 1))))
    (.app (.lam (.app (.lam
      (.app (.app (.bvar 4) (.binop .minus (.bvar 3) (.lit (.int 1))))
        (.cond (.binop .le (.lit (.int observed)) (.bvar 0))
          (.binop .plus (.bvar 2) (.lit (.int 1))) (.bvar 2))))
      (.app statistic.fst (.bvar 0))))
      (.app Occil.shuffle (listVal input xs).fst)))))

private def loopValue {rT : Type _} [ProbLangℝ rT] (input : α → Val rT)
    (xs : List α) (statistic : Val rT) (observed : ℤ) (replicates : ℕ) : Val rT :=
  ⟨loop input xs statistic observed replicates, .fix (by is_lc), by is_lc⟩

private theorem loopValue_fst {rT : Type _} [ProbLangℝ rT] (input : α → Val rT)
    (xs : List α) (statistic : Val rT) (observed : ℤ) (replicates : ℕ) :
    (loopValue input xs statistic observed replicates).fst =
      loop input xs statistic observed replicates := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (input : α → Val rT) (xs : List α)
    (statistic : Val rT) (S : List α → ℤ)
    (hstat : ∀ ys, ⊢ tglWp E pl(&statistic.fst &(listVal input ys).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (S ys)⌝)))
    (replicates n z : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F (z + k) ∂law xs S n) -∗
      tglWp E pl(&(loop input xs statistic (S xs) replicates)
        #int (n : ℤ) #int (z : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = encode replicates k⌝ ∗ ↯ (F k))) := by
  induction n generalizing z with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists z
    isimp only [law, Binomial.expectation_zero, Nat.add_zero] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    iintro Hcredit
    rw [← loopValue_fst]
    twp_step
    simp only [Exp.open', Exp.openRec, Shuffle.shuffle_openRec,
      ProbLang.openRec_val_fst]
    iterate 4 twp_pure
    twp_bind pl(&Occil.shuffle &(listVal input xs).fst)
    isimp only [← expectation xs S n z F] at Hcredit
    iapply (Shuffle.shuffle_distSpec E input xs).wp
      (fun σ => ∫⁻ k, F (if exceeds xs S σ then z + 1 + k else z + k) ∂law xs S n)
      (measurable_of_countable _) _ $$ Hcredit
    iintro %σ Hcredit
    twp_pure
    twp_bind pl(&statistic.fst &(listVal input (Shuffle.output xs σ)).fst)
    iapply tglWp_wand
    isplitl []
    · iapply hstat (Shuffle.output xs σ)
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    cases hσ : decide (S xs ≤ S (Shuffle.output xs σ)) with
    | false =>
      twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      simp only [Exp.ofVal]
      rw [loopValue_fst]
      isimp only [exceeds, hσ, Bool.false_eq_true, ite_false] at Hcredit
      iapply IH z $$ Hcredit
    | true =>
      twp_pure
      twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add_one]
      simp only [Exp.ofVal]
      rw [loopValue_fst]
      isimp only [exceeds, hσ, ite_true] at Hcredit
      iapply IH (z + 1) $$ Hcredit

/-- Every replicate count, with arbitrary observations and a deterministic statistic. -/
theorem permutationTest_distSpec (E : CoPset) (input : α → Val rT) (xs : List α)
    (statistic : Val rT) (S : List α → ℤ)
    (hstat : ∀ ys, ⊢ tglWp E pl(&statistic.fst &(listVal input ys).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (S ys)⌝))) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.permutationTest &(listVal input xs).fst &statistic.fst #int (n : ℤ))
      (law xs S n) (encode n) where
  spec F _ := by
    have hloop := twp_loop (rT := rT) (GF := GF) E input xs statistic S hstat n n 0 F
    simp [loop] at hloop
    iintro Hcredit
    iterate 5 twp_pure
    twp_bind pl(&statistic.fst &(listVal input xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply hstat xs
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    simp only [Shuffle.shuffle_openRec, Shuffle.shuffle_closeRec]
    iapply hloop $$ Hcredit

end specification

end

end SampLib.PermutationTest
