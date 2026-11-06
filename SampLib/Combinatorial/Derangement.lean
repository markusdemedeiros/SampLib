import SampLib.Combinatorial.Support.IntegerRange
import SampLib.Continuous.Rejection
import SampLib.Common.Syntax.Shuffle
import SampLib.Combinatorial.Support.ShuffleVector
import SampLib.Common.Syntax.Rejection
import SampLib.Combinatorial.Laws.Derangements
import SampLib.Combinatorial.Laws.DerangementCheck
import Samplers.Combinatorial.Permutations

/-! # Uniform fixed-point-free position permutations -/

open ProbLang Equiv
open scoped ENNReal Classical

namespace SampLib.Derangement

noncomputable section

private def check {rT : Type} : Exp rT := pl%
  rec go xs i := case! xs | inl(u) => #true | inr(p) =>
    if fst(p) = i then #false else go (snd(p)) (i + #1)

private theorem int_eq_test {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = decide (a = b) := by
  change (a == b) = decide (a = b)
  exact Bool.beq_eq_decide_eq a b

def output {rT : Type} [ProbLangℝ rT] (n : ℕ) (σ : Perm (Fin n)) : Val rT :=
  listVal Val.int (List.ofFn (fun i => ((σ i).val : ℤ)))

private def proposal {rT : Type} (n : ℕ) : Val rT :=
  ⟨pl(fun u, &Occil.shuffle (&Occil.intRange #0 #int (n : ℤ))),
    .lam (by is_lc), by is_lc⟩

private def accept {rT : Type} : Val rT :=
  ⟨pl(fun xs, &(check (rT := rT)) xs #0), .lam (by is_lc), by is_lc⟩

private theorem domain_guard {rT : Type} [BEq rT] (n : ℕ) (hn : n ≠ 1) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = false := by
  change ((n : ℤ) == 1) = false
  exact beq_eq_false_iff_ne.mpr (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_check (E : CoPset) (xs : List ℤ) (start : ℤ) :
    ⊢ tglWp E pl(&(check (rT := rT)) &(listVal Val.int xs).fst #int start)
      (fun v => iprop(⌜v = Val.bool (decide (avoids xs start))⌝)) := by
  induction xs generalizing start with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [avoids]
  | cons x xs IH =>
    simp only [listVal]
    twp_pures
    rw [int_eq_test, avoids_cons_test]
    by_cases hx : x = start
    · simp only [hx, decide_true, ite_true]
      twp_pures
      twp_value
      imodintro
      itrivial
    · simp only [hx, decide_false, ite_false]
      iterate 3 twp_pure
      have hrec := IH (start + 1)
      simp [check, Exp.close, Exp.closeRec] at hrec
      simp only [Exp.ofVal]
      iapply hrec

private theorem twp_accept (E : CoPset) (n : ℕ) (σ : Perm (Fin n)) :
    ⊢ tglWp E pl(&(accept (rT := rT)).fst &(output n σ).fst)
      (fun v => iprop(⌜v = Val.bool (decide (σ ∈ derangements (Fin n)))⌝)) := by
  twp_pure
  have hcheck := twp_check (GF := GF) E (List.ofFn (fun i => ((σ i).val : ℤ))) 0
  simp only [avoids_ofFn] at hcheck
  simp [check, Exp.close, Exp.closeRec] at hcheck
  simp [output, check, Exp.close, Exp.closeRec]
  iapply hcheck

variable [ProbLangDist.IsUniformInt rT]

private theorem proposal_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&(proposal (rT := rT) n).fst #())
      (Permutations.law n) (output n) where
  spec F _ := by
    iintro Hcredit
    twp_pure
    simp only [Shuffle.shuffle_openRec, Shuffle.shuffle_closeRec,
      IntegerRange.intRange_openRec, IntegerRange.intRange_closeRec]
    twp_bind pl(&Occil.intRange #0 #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · have hrange := IntegerRange.twp_intRange (GF := GF) E 0 n
      simp only [zero_add] at hrange
      iapply hrange
    iintro %v %hv
    subst v
    simp only [interval_ofFn, zero_add]
    have hshuffle := Shuffle.shuffleVector_distSpec (GF := GF) E Val.int
      (fun i : Fin n => (i.val : ℤ))
    simp only [Function.comp_def] at hshuffle
    isimp only [output, Exp.ofVal]
    iapply hshuffle.spec F (measurable_of_countable _) $$ Hcredit

/-- The proposal is independent on each retry; only fixed-point-free proposals return. -/
theorem twp_derangement (E : CoPset) (n : ℕ) (hn : n ≠ 1)
    (F : Perm (Fin n) → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ σ, F σ ∂DerangementLaw.law n hn) -∗
      tglWp E pl(&Occil.derangement #int (n : ℤ))
        (fun v => iprop(∃ σ : Perm (Fin n), ⌜v = output n σ⌝ ∗ ↯ (F σ))) := by
  have hreject := Rejection.twp_rejection (GF := GF) E (Permutations.law n)
    (derangements (Fin n)) (Set.to_countable _).measurableSet
    (DerangementLaw.acceptance_nonzero n hn) (output n) (proposal n) accept
    (proposal_distSpec E n) (twp_accept E n) F (measurable_of_countable _)
  simp [proposal, accept, check, Exp.close, Exp.closeRec] at hreject
  simp only [Rejection.credit, Rejection.law] at hreject
  iintro Hcredit
  twp_pure
  simp only [Rejection.rejection_openRec, Rejection.rejection_closeRec,
    Shuffle.shuffle_openRec, Shuffle.shuffle_closeRec,
    IntegerRange.intRange_openRec, IntegerRange.intRange_closeRec]
  twp_pures
  rw [domain_guard n hn]
  simp only [Bool.or_false]
  iterate 2 twp_pure
  simp only [Rejection.rejection_openRec, Shuffle.shuffle_openRec,
    IntegerRange.intRange_openRec]
  isimp only [DerangementLaw.law] at Hcredit
  iapply hreject $$ Hcredit

/-- Uniform derangements, including the empty permutation and excluding the impossible singleton. -/
theorem derangement_distSpec (E : CoPset) (n : ℕ) (hn : n ≠ 1) :
    IsDistSpec (GF := GF) E pl(&Occil.derangement #int (n : ℤ))
      (DerangementLaw.law n hn) (output n) where
  spec F _ := wand_entails (twp_derangement E n hn F)

end specification

end

end SampLib.Derangement
