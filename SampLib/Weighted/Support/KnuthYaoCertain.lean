import SampLib.Weighted.Syntax.KnuthYao
import SampLib.Weighted.Laws.WeightedSums

/-! # The source's certain-category shortcut, including arbitrary zero-weight rows -/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.KnuthYao

noncomputable section

/-- The first row equal to the total, exactly as in the source's scan. -/
def certain : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | w :: ws, T => if w = T then some 0 else (certain ws T).map Nat.succ

theorem certain_none (ws : List ℕ) (T : ℕ) :
    certain ws T = none ↔ ∀ w ∈ ws, w ≠ T := by
  induction ws with
  | nil => simp [certain]
  | cons w ws ih => by_cases h : w = T <;> simp [certain, h, ih]

theorem certain_some (ws : List ℕ) (T i : ℕ) (hi : certain ws T = some i) :
    ws[i]? = some T := by
  induction ws generalizing i with
  | nil => simp [certain] at hi
  | cons w ws ih =>
    by_cases h : w = T
    · simp only [certain, h, ite_true, Option.some.injEq] at hi
      subst i
      simp [h]
    · simp only [certain, h, ite_false] at hi
      cases hc : certain ws T with
      | none => simp [hc] at hi
      | some j =>
        simp only [hc, Option.map_some, Option.some.injEq] at hi
        subst i
        exact ih j hc

def certainInt (offset : ℕ) : Option ℕ → ℤ
  | none => -1
  | some i => ((offset + i : ℕ) : ℤ)

private theorem weight_test {rT : Type} [BEq rT] (w T : ℕ) :
    ((BaseLit.int (w : ℤ) : BaseLit rT) == .int (T : ℤ)) = decide (w = T) := by
  change decide ((w : ℤ) = (T : ℤ)) = decide (w = T)
  exact decide_eq_decide.mpr (by omega)

/-- A certain row carries all the categorical mass, even when other rows have infinite credits. -/
theorem certain_expectation (ws : List ℕ) (hT : 0 < ws.sum) (i : ℕ)
    (hi : certain ws ws.sum = some i) (F : ℕ → ℝ≥0∞) :
    (∫⁻ j, F j ∂WeightedChoice.law ws) = F i := by
  let : NeZero ws.sum := ⟨Nat.ne_of_gt hT⟩
  have hm : WeightedChoice.law ws {i} = 1 := by
    rw [WeightedChoice.law_singleton, certain_some ws ws.sum i hi]
    simp only [Option.getD_some]
    exact ENNReal.div_self (by exact_mod_cast Nat.ne_of_gt hT) (by finiteness)
  have ha : ∀ᵐ j ∂WeightedChoice.law ws, j = i :=
    (mem_ae_iff_prob_eq_one (measurableSet_singleton i)).mpr hm
  rw [lintegral_congr_ae (ha.mono (fun j hj => congrArg F hj))]
  simp

/-- With no certain row, every row probability has vanishing integer part. -/
theorem proper_of_none (ws : List ℕ) (hnone : certain ws ws.sum = none) :
    ∀ i, ws.get i < ws.sum := by
  intro i
  have hle : ws.get i ≤ ws.sum := List.le_sum_of_mem (List.get_mem _ _)
  have hne := (certain_none ws ws.sum).mp hnone (ws.get i) (List.get_mem _ _)
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Deterministic execution of the source's scan for a certain row. -/
theorem twp_find (E : CoPset) (ws : List ℕ) (T offset : ℕ) :
    ⊢ tglWp E pl(&(Program.find T) &(listVal (fun w : ℕ => Val.int w) ws).fst
      #int (offset : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (certainInt offset (certain ws T))⌝)) := by
  induction ws generalizing offset with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | cons w ws ih =>
    simp only [listVal]
    twp_pures
    rw [weight_test]
    by_cases h : w = T
    · rw [decide_eq_true h]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp [certain, h, certainInt]
    · rw [decide_eq_false h]
      iterate 3 twp_pure
      rw [← Nat.cast_add_one]
      simp only [Exp.ofVal]
      ieval (
        change _ ⊢ tglWp E
          pl(&(Program.find T) &(listVal (fun w : ℕ => Val.int w) ws).fst
            #int ((offset + 1 : ℕ) : ℤ)) _)
      iapply tglWp_wand
      isplitl []
      · iapply ih (offset + 1)
      iintro %v %hv
      ipureintro
      simp only [certain, h, ite_false]
      have he (r : Option ℕ) : certainInt offset (r.map Nat.succ) = certainInt (offset + 1) r := by
        cases r <;> simp [certainInt, add_comm, add_left_comm]
      rw [he]
      exact hv

end specification

end

end SampLib.KnuthYao
