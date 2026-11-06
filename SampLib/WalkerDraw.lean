import SampLib.AliasTable

/-! # Walker draws from owned alias tables -/

open ProbLang
open scoped ENNReal

namespace SampLib.WalkerDraw

noncomputable section

abbrev natVal {rT : Type} [ProbLangℝ rT] (n : ℕ) : Val rT := Val.int n

/-- Walker always draws a ticket, including columns whose alias is their own index. -/
def draw {rT : Type} (n total : ℕ) (probability aliases : Loc) : Val rT :=
  ⟨pl(fun u,
    let i := &Occil.uniformInt #int (n : ℤ);
    if &Occil.uniformInt #int (total : ℤ) < !(#loc probability +ₗ i) then i
    else !(#loc aliases +ₗ i)), .lam (by is_lc), by is_lc⟩

private def tickets {n total : ℕ} (t : AliasMass.Table n total) (F : ℕ → ℝ≥0∞)
    (i : Fin n) (k : ℕ) : ℝ≥0∞ :=
  if k < t.threshold i then F i.val else F (t.target i).val

private theorem ticket_expectation {n total : ℕ} (t : AliasMass.Table n total)
    (ht : 0 < total) (F : ℕ → ℝ≥0∞) (i : Fin n) :
    (∑ k ∈ Finset.range total, tickets t F i k) / total = t.columnCredit F i := by
  rw [AliasMass.columnCredit_eq t ht F i]
  simpa only [tickets, ENNReal.natCast_sub] using
    congrArg (fun x : ℝ≥0∞ => x / total)
      (AliasMass.threshold_sum total (t.threshold i) (t.threshold_le i) (F i.val)
        (F (t.target i).val))

private theorem length_pos (ws : List ℕ) (h : 0 < ws.sum) : 0 < ws.length := by
  cases ws with
  | nil => simp at h
  | cons w ws => simp

private theorem ticket_test (k cut : ℕ) :
    decide ((k : ℤ) < (cut : ℤ)) = decide (k < cut) := by simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Two uniform draws read the table while preserving it for subsequent samples. -/
theorem draw_ownedDistSpec (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum)
    (t : AliasMass.Table ws.length ws.sum)
    (hmass : ∀ i, t.mass i = ws.length * ws.get i) (probability aliases : Loc) :
    letI : NeZero ws.sum := ⟨hs.ne'⟩
    IsOwnedDistSpec (rT := rT) (GF := GF) E (AliasTable.owns t probability aliases)
      pl(&(draw (rT := rT) ws.length ws.sum probability aliases).fst #())
      (WeightedChoice.law ws) natVal := by
  let : NeZero ws.sum := ⟨hs.ne'⟩
  refine ⟨fun F _ => ?_⟩
  isimp only [AliasTable.owns]
  iintro ⟨⟨Hprobability, Haliases⟩, Hcredit⟩
  twp_pure
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
  have htickets := ticket_expectation t hs F j
  simp only [j] at htickets
  isimp only [AliasMass.Table.columnCreditNat, dite_eq_left hi] at Hcredit
  twp_pure
  twp_bind pl(!(#loc probability +ₗ #int (i : ℤ)))
  iapply tglWp_wand
  isplitl [Hprobability]
  · iapply (Array.twp_load_ofFn E probability (fun k => (natVal (t.threshold k) : Val rT)) j)
      $$ Hprobability
  iintro %v ⟨%hv, Hprobability⟩
  subst v
  twp_bind pl(&Occil.uniformInt #int (ws.sum : ℤ))
  isimp only [← htickets] at Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E ws.sum hs (tickets t F j)) $$ Hcredit
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
    isimp only [tickets, ite_eq_left hk] at Hcredit
    iframe Hcredit Hprobability Haliases
    itrivial
  · rw [decide_eq_false hk]
    twp_pure
    twp_bind pl(!(#loc aliases +ₗ #int (i : ℤ)))
    iapply tglWp_wand
    isplitl [Haliases]
    · iapply (Array.twp_load_ofFn E aliases
        (fun index => (Val.int (t.target index).val : Val rT)) j) $$ Haliases
    iintro %v ⟨%hv, Haliases⟩
    iapply (tglWp_value (v := v))
    iexists (t.target j).val
    isimp only [tickets, ite_eq_right hk] at Hcredit
    iframe Hcredit Hprobability Haliases
    iframe %hv

end specification

end

end SampLib.WalkerDraw
