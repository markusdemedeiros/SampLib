import SampLib.Core.ArrayOwnership
import SampLib.Combinatorial.Laws.ReservoirTickets
import SampLib.Uniform.UniformInt
import Samplers.Combinatorial.Basic

/-! # Loop invariants for the Algorithm R scan

The initial stream prefix fills the reservoir array. Every later element then makes one
independent replacement decision, which pays the remaining scan credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Reservoir

noncomputable section

/-- The scan loop of `Occil.reservoir`, over an allocated reservoir array. -/
def scan {rT : Type} (l : Loc) (k : ℕ) : Exp rT := pl%
  rec go ys i := case! ys | inl(u) => #() | inr(p) =>
    if i < #int (k : ℤ) then
      ((#loc l +ₗ i) ← fst(p); go (snd(p)) (i + #1))
    else
      let j := &Occil.uniformInt (i + #1);
      if j < #int (k : ℤ) then
        ((#loc l +ₗ j) ← fst(p); go (snd(p)) (i + #1))
      else go (snd(p)) (i + #1)

private theorem initial_guard (i n k : ℕ) (h : i + (n + 1) = k) :
    decide ((i : ℤ) < (k : ℤ)) = true := by
  exact decide_eq_true (by omega)

private theorem initial_next (i n k : ℕ) (h : i + (n + 1) = k) :
    (i + 1) + n = k := by omega

private theorem future_guard (start k : ℕ) (h : k ≤ start) :
    decide ((start : ℤ) < (k : ℤ)) = false := decide_eq_false (by omega)

private theorem nat_lt_test (a b : ℕ) :
    decide ((a : ℤ) < (b : ℤ)) = decide (a < b) := by simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The initial stream prefix fills the array before any random replacements. -/
private theorem twp_initial (E : CoPset) (l : Loc) (k : ℕ)
    (xs ys : List (Val rT)) (i : ℕ) (hi : i + xs.length = k)
    (Φ : Val rT → IProp GF) :
    ⊢ Array.owns (l + (i : ℤ)) (List.replicate xs.length Val.unit) -∗
      (Array.owns (l + (i : ℤ)) xs -∗
        tglWp E pl(&(scan (rT := rT) l k) &(listVal id ys).fst #int (k : ℤ)) Φ) -∗
      tglWp E pl(&(scan (rT := rT) l k) &(listVal id (xs ++ ys)).fst #int (i : ℤ)) Φ := by
  induction xs generalizing i with
  | nil =>
    have he : i = k := by simpa using hi
    subst i
    simp only [List.nil_append, List.length_nil, List.replicate_zero]
    iintro Harray Hcont
    iapply Hcont $$ Harray
  | cons x xs IH =>
    iintro Harray Hcont
    isimp only [List.length_cons, List.replicate_succ, Array.owns] at Harray
    ihave ⟨Hx, Htail⟩ := Harray
    simp only [List.cons_append, listVal]
    twp_pures
    rw [initial_guard i xs.length k hi]
    twp_pures
    simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
    twp_bind (Exp.store pl(#loc (l + (i : ℤ))) (Exp.ofVal x))
    iapply twp_store
    iframe Hx
    iintro Hx
    iterate 3 twp_pure
    rw [← Nat.cast_add_one]
    have hrec := IH (i + 1) (initial_next i xs.length k hi)
    simp [scan, Exp.close, Exp.closeRec] at hrec
    simp only [UniformInt.uniformInt_openRec, Nat.cast_add_one, Exp.ofVal]
    isimp only [add_assoc] at Htail
    iapply hrec $$ Htail
    iintro Hfilled
    isimp [scan, Exp.close, Exp.closeRec] at Hcont
    iapply Hcont
    isimp only [Array.owns, add_assoc]
    iframe Hx Hfilled

/-- Every remaining stream element makes one independent replacement decision. -/
private theorem twp_future (E : CoPset) (l : Loc) (k : ℕ)
    (decode : ℕ → Val rT) (start steps : ℕ) (hs : k ≤ start)
    (s : ReservoirLaw.Slots k) (F : ReservoirLaw.Slots k → ℝ≥0∞) :
    Array.owns l (List.ofFn (decode ∘ s)) ⊢ ↯ (ReservoirLaw.finish start steps s F) -∗
      tglWp E pl(&(scan (rT := rT) l k)
        &(listVal id ((List.range' start steps).map decode)).fst #int (start : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗ ∃ t : ReservoirLaw.Slots k,
          Array.owns l (List.ofFn (decode ∘ t)) ∗ ↯ (F t))) := by
  induction steps generalizing start s with
  | zero =>
    iintro Harray Hcredit
    simp only [List.range'_zero, List.map_nil, listVal]
    twp_pures
    twp_value
    imodintro
    isplit
    · itrivial
    · iexists s
      isimp only [ReservoirLaw.finish_zero] at Hcredit
      iframe Harray Hcredit
  | succ steps IH =>
    iintro Harray Hcredit
    simp only [List.range'_succ, List.map_cons, listVal]
    twp_pures
    rw [future_guard start k hs]
    iterate 2 twp_pure
    simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
    rw [← Nat.cast_add_one]
    twp_bind pl(&Occil.uniformInt #int ((start + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (UniformInt.twp_uniformInt E (start + 1) (Nat.succ_pos start)
        (ticketCredit start steps s F))
      rw [ticket_expectation]
      iexact Hcredit
    iintro %v ⟨%j, %hv, %hj, Hcredit⟩
    subst v
    twp_pures
    rw [nat_lt_test]
    by_cases hjk : j < k
    · simp only [hjk, decide_true]
      iterate 2 twp_pure
      twp_bind pl((#loc l +ₗ #int (j : ℤ)) ← &(decode start).fst)
      iapply tglWp_wand
      isplitl [Harray]
      · iapply (Array.twp_store_ofFn E l (decode ∘ s) ⟨j, hjk⟩ (decode start)) $$ Harray
      iintro %w ⟨%hw, Harray⟩
      subst w
      iterate 3 twp_pure
      rw [← Nat.cast_add_one]
      isimp only [encoded_update decode s ⟨j, hjk⟩ start] at Harray
      isimp only [ticketCredit, Choice.position_of_lt j hj,
        ReservoirLaw.advance_lt s ⟨j, hj⟩ hjk] at Hcredit
      have hrec := IH (start + 1) (Nat.le_succ_of_le hs)
        (Function.update s ⟨j, hjk⟩ start)
      simp [-List.ofFn_succ, scan, Exp.close, Exp.closeRec] at hrec
      simp only [UniformInt.uniformInt_openRec, Nat.cast_add_one, Exp.ofVal]
      iapply hrec $$ Harray Hcredit
    · simp only [hjk, decide_false]
      iterate 3 twp_pure
      rw [← Nat.cast_add_one]
      isimp only [ticketCredit, Choice.position_of_lt j hj,
        ReservoirLaw.advance_ge s ⟨j, hj⟩ (Nat.le_of_not_gt hjk)] at Hcredit
      have hrec := IH (start + 1) (Nat.le_succ_of_le hs) s
      simp [-List.ofFn_succ, scan, Exp.close, Exp.closeRec] at hrec
      simp only [UniformInt.uniformInt_openRec, Nat.cast_add_one, Exp.ofVal]
      iapply hrec $$ Harray Hcredit

/-- The whole scan from an empty reservoir pays the scan's finite-horizon credit. -/
theorem twp_scan (E : CoPset) (l : Loc) (decode : ℕ → Val rT)
    (n k : ℕ) (hkn : k ≤ n) (F : ReservoirLaw.Slots k → ℝ≥0∞) :
    Array.owns l (List.replicate k Val.unit) ⊢
      ↯ (ReservoirLaw.finish k (n - k) (ReservoirLaw.initial k) F) -∗
      tglWp E pl(&(scan (rT := rT) l k)
        &(listVal id ((List.range' 0 n).map decode)).fst #0)
        (fun v => iprop(⌜v = Val.unit⌝ ∗ ∃ t : ReservoirLaw.Slots k,
          Array.owns l (List.ofFn (decode ∘ t)) ∗ ↯ (F t))) := by
  iintro Harray Hcredit
  rw [stream_split decode n k hkn]
  have hinit := twp_initial (GF := GF) E l k
    ((List.range' 0 k).map decode) ((List.range' k (n - k)).map decode) 0 (by simp)
    (fun v => iprop(⌜v = Val.unit⌝ ∗ ∃ t : ReservoirLaw.Slots k,
      Array.owns l (List.ofFn (decode ∘ t)) ∗ ↯ (F t)))
  simp only [Nat.cast_zero, add_zero, List.length_map, List.length_range'] at hinit
  iapply hinit $$ Harray
  iintro Hfilled
  isimp only [stream_initial] at Hfilled
  iapply (twp_future E l k decode k (n - k) le_rfl (ReservoirLaw.initial k) F)
    $$ Hfilled Hcredit

end specification

end

end SampLib.Reservoir
