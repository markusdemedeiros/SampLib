import SampLib.Discrete.Support.NatCounters
import Samplers.Discrete.Urns
import Metrology.Iris.LocalBI

/-! Deterministic validation and weight construction for natural multicolor urns. -/

open ProbLang

namespace SampLib.NatUrnOps

private def valid : List ℕ → List ℕ → Bool
  | [], [] => true
  | _ :: pop, o :: odds => if o = 0 then false else valid pop odds
  | _, _ => false

private theorem valid_eq_true (pop odds : List ℕ) :
    valid pop odds = true ↔ pop.length = odds.length ∧ ∀ o ∈ odds, 0 < o := by
  induction pop generalizing odds with
  | nil => cases odds <;> simp [valid]
  | cons p pop IH =>
    cases odds with
    | nil => simp [valid]
    | cons o odds =>
      by_cases ho : o = 0
      · subst o; simp [valid]
      · simp [valid, ho, IH, Nat.pos_of_ne_zero ho]

private theorem odds_test (o : ℕ) :
    Bool.or false (decide ((o : ℤ) ≤ 0)) = decide (o = 0) := by
  simp only [Bool.false_or]
  exact decide_eq_decide.mpr (by omega)

private theorem cons_value {rT : Type _} [ProbLangℝ rT] (x : ℕ) (xs : List ℕ) :
    (pl(inr((#int (x : ℤ), {Exp.ofVal (NatCounters.encode xs)}))) : Exp rT) =
      Exp.ofVal (NatCounters.encode (x :: xs)) := by
  simp [NatCounters.encode, listVal, Exp.ofVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_valid (E : CoPset) (pop odds : List ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.validUrn &(NatCounters.encode pop).fst
      &(NatCounters.encode odds).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (valid pop odds)⌝)) := by
  induction pop generalizing odds with
  | nil =>
    cases odds <;> simp only [NatCounters.encode, listVal]
    all_goals
      twp_pures
      twp_value
      imodintro
      ipureintro
      rfl
  | cons p pop IH =>
    cases odds with
    | nil =>
      simp only [NatCounters.encode, listVal]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rfl
    | cons o odds =>
      simp only [NatCounters.encode, listVal]
      twp_pures
      rw [odds_test o]
      by_cases ho : o = 0
      · rw [decide_eq_true ho]
        twp_pures
        twp_value
        imodintro
        ipureintro
        simp [valid, ho]
      · rw [decide_eq_false ho]
        iterate 3 twp_pure
        have h := IH odds
        simp only [NatCounters.encode] at h
        simp only [valid, ite_eq_right ho, Exp.ofVal]
        exact h

/-- Matching nonnegative populations and positive odds pass the actual urn validator. -/
theorem twp_validUrn (E : CoPset) (pop odds : List ℕ) (hlen : pop.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.validUrn &(NatCounters.encode pop).fst
      &(NatCounters.encode odds).fst) (fun v : Val rT => iprop(⌜v = Val.bool true⌝)) := by
  simpa only [(valid_eq_true pop odds).mpr ⟨hlen, hodds⟩] using twp_valid E pop odds

/-- The integer list routine computes the pointwise population-times-odds weights. -/
theorem twp_urnWeights (E : CoPset) (pop odds : List ℕ) (hlen : pop.length ≤ odds.length) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.urnWeights &(NatCounters.encode pop).fst
      &(NatCounters.encode odds).fst)
      (fun v : Val rT => iprop(⌜v = NatCounters.encode (List.zipWith Nat.mul pop odds)⌝)) := by
  induction pop generalizing odds with
  | nil =>
    simp only [NatCounters.encode, listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | cons p pop IH =>
    cases odds with
    | nil => simp at hlen
    | cons o odds =>
      simp only [NatCounters.encode, listVal]
      iterate 9 twp_pure
      twp_bind pl(&Occil.DiscreteExtra.urnWeights &(NatCounters.encode pop).fst
        &(NatCounters.encode odds).fst)
      iapply tglWp_wand
      isplitl []
      · iapply IH odds (by simpa using hlen)
      iintro %v %hv
      subst v
      iterate 3 twp_pure
      rw [← Nat.cast_mul, cons_value]
      iapply tglWp_value
      ipureintro
      rfl

end specification

end SampLib.NatUrnOps
