import SampLib.ArrayOwnership
import SampLib.OwnedDistSpec
import SampLib.Distributions.AliasMass
import Samplers.Weighted.Aliases

/-! # Reading heap-backed alias tables without consuming their ownership -/

open ProbLang
open scoped ENNReal

namespace SampLib.AliasTable

noncomputable section

/-- The returned table contains two sizes and two owned heap locations. -/
def value {rT : Type _} [ProbLangℝ rT] (n total : ℕ) (probability aliases : Loc) : Val rT :=
  .pair (.int n) (.pair (.int total) (.pair (.loc probability) (.loc aliases)))

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- Ownership of every threshold and alias entry. -/
def owns {n total : ℕ} (t : AliasMass.Table n total) (probability aliases : Loc) : IProp GF :=
  iprop(Array.owns probability (List.ofFn (fun i => (Val.int (t.threshold i) : Val rT))) ∗
    Array.owns aliases (List.ofFn (fun i => (Val.int (t.target i).val : Val rT))))

end ownership

private theorem length_pos (ws : List ℕ) (hs : 0 < ws.sum) : 0 < ws.length := by
  cases ws with
  | nil => simp at hs
  | cons w ws => simp

private theorem index_test {rT : Type _} [ProbLangℝ rT] {n : ℕ} (i j : Fin n) :
    ((BaseLit.int (i.val : ℤ) : BaseLit rT) == .int (j.val : ℤ)) = decide (i = j) := by
  change ((i.val : ℤ) == (j.val : ℤ)) = decide (i = j)
  simp [beq_eq_decide, Fin.ext_iff]

private theorem ticket_test (k cut : ℕ) :
    decide ((k : ℤ) < (cut : ℤ)) = decide (k < cut) := by simp

private theorem ticket_sum (total cut : ℕ) (hcut : cut ≤ total) (x y : ℝ≥0∞) :
    (∑ k ∈ Finset.range total, if k < cut then x else y) =
      (cut : ℝ≥0∞) * x + ((total - cut : ℕ) : ℝ≥0∞) * y := by
  simpa only [ENNReal.natCast_sub] using AliasMass.threshold_sum total cut hcut x y

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Draw a category while retaining both heap arrays for the next call. -/
theorem voseDraw_ownedDistSpec (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum)
    (t : AliasMass.Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (probability aliases : Loc) :
    letI : NeZero ws.sum := ⟨hs.ne'⟩
    IsOwnedDistSpec (rT := rT) (GF := GF) E (owns (rT := rT) (GF := GF) t probability aliases)
      pl(&Occil.WeightedVariants.voseDraw &(value ws.length ws.sum probability aliases).fst #())
      (WeightedChoice.law ws) (fun i : ℕ => Val.int i) := by
  let : NeZero ws.sum := ⟨hs.ne'⟩
  refine ⟨fun F _ => ?_⟩
  isimp only [owns]
  iintro ⟨⟨Hprobability, Haliases⟩, Hcredit⟩
  iterate 15 twp_pure
  simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  twp_bind pl(&Occil.uniformInt #int (ws.length : ℤ))
  isimp only [← AliasMass.expectation_range ws hs t hmass F] at Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E ws.length (length_pos ws hs)
      (t.columnCreditNat F)) $$ Hcredit
  iintro %v ⟨%i, %hv, %hi, Hcredit⟩
  subst v
  let j : Fin ws.length := ⟨i, hi⟩
  isimp only [AliasMass.Table.columnCreditNat, dite_eq_left hi] at Hcredit
  twp_pure
  twp_bind pl(!(#loc aliases +ₗ #int (i : ℤ)))
  iapply tglWp_wand
  isplitl [Haliases]
  · iapply (Array.twp_load_ofFn E aliases
      (fun k : Fin ws.length => Val.int ((t.target k).val : ℤ)) j) $$ Haliases
  iintro %v ⟨%hv, Haliases⟩
  subst v
  iterate 2 twp_pure
  rw [index_test j (t.target j)]
  by_cases heq : j = t.target j
  · have heq' : (⟨i, hi⟩ : Fin ws.length) = t.target ⟨i, hi⟩ := heq
    rw [decide_eq_true heq]
    twp_pures
    twp_value
    imodintro
    iexists i
    isimp only [AliasMass.Table.columnCredit, ite_eq_left heq'] at Hcredit
    iframe Hcredit Hprobability Haliases
    itrivial
  · have heq' : (⟨i, hi⟩ : Fin ws.length) ≠ t.target ⟨i, hi⟩ := heq
    rw [decide_eq_false heq]
    twp_pure
    twp_bind pl(!(#loc probability +ₗ #int (i : ℤ)))
    iapply tglWp_wand
    isplitl [Hprobability]
    · iapply (Array.twp_load_ofFn E probability
        (fun k : Fin ws.length => Val.int (t.threshold k)) j) $$ Hprobability
    iintro %v ⟨%hv, Hprobability⟩
    subst v
    twp_bind pl(&Occil.uniformInt #int (ws.sum : ℤ))
    isimp only [AliasMass.Table.columnCredit, ite_eq_right heq'] at Hcredit
    have htickets := ticket_sum ws.sum (t.threshold j) (t.threshold_le j)
      (F i) (F (t.target j))
    simp only [j] at htickets
    isimp only [← htickets] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (UniformInt.twp_uniformInt E ws.sum hs
        (fun k => if k < t.threshold j then F i else F (t.target j))) $$ Hcredit
    iintro %v ⟨%k, %hv, %_hk, Hcredit⟩
    subst v
    twp_pure
    rw [ticket_test]
    by_cases hk : k < t.threshold j
    · rw [decide_eq_true hk]
      twp_pures
      twp_value
      imodintro
      iexists i
      isimp only [ite_eq_left hk] at Hcredit
      iframe Hcredit Hprobability Haliases
      itrivial
    · rw [decide_eq_false hk]
      twp_pures
      twp_value
      imodintro
      iexists (t.target j).val
      isimp only [ite_eq_right hk] at Hcredit
      iframe Hcredit Hprobability Haliases
      itrivial

end specification

end

end SampLib.AliasTable
