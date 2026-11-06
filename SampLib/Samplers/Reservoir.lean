import SampLib.ArrayOwnership
import SampLib.Distributions.Permutations
import SampLib.Distributions.Reservoir
import SampLib.Samplers.Choice
import SampLib.Samplers.UniformInt
import SampLib.Syntax.Arrays
import Samplers.Combinatorial.Basic

/-! # Reservoir sampling with the exact law of its ordered slots

The selected position subset is uniform. Retained initial entries keep their
original slots; selected later entries are uniform among the remaining slots.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Reservoir

noncomputable section

private def scan {rT : Type} (l : Loc) (k : ℕ) : Exp rT := pl%
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

private def ticketCredit {k : ℕ} (start steps : ℕ) (s : ReservoirLaw.Slots k)
    (F : ReservoirLaw.Slots k → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  ReservoirLaw.finish (start + 1) steps
    (ReservoirLaw.advance start s (Choice.position (start + 1) j)) F

private theorem ticket_expectation {k : ℕ} (start steps : ℕ) (s : ReservoirLaw.Slots k)
    (F : ReservoirLaw.Slots k → ℝ≥0∞) :
    (∑ j ∈ Finset.range (start + 1), ticketCredit start steps s F j) /
      ((start + 1 : ℕ) : ℝ≥0∞) = ReservoirLaw.finish start (steps + 1) s F := by
  rw [← Fin.sum_univ_eq_sum_range (ticketCredit start steps s F) (start + 1),
    ReservoirLaw.finish_step]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [ticketCredit, Choice.position_of_lt j.val j.isLt]

private theorem encoded_update {α : Type*} (decode : ℕ → α) {k : ℕ}
    (s : ReservoirLaw.Slots k) (j : Fin k) (start : ℕ) :
    (List.ofFn (decode ∘ s)).set j (decode start) =
      List.ofFn (decode ∘ Function.update s j start) := by
  rw [Function.comp_update, Permutations.ofFn_update]

/-- Original-position decoding; the fallback lies outside the target law's support. -/
def entry {rT : Type} [ProbLangℝ rT] (encode : α → Val rT) (xs : List α)
    (j : ℕ) : Val rT := ((xs.map encode)[j]?).getD Val.unit

/-- Decode the selected original positions in the reservoir's actual slot order. -/
def output {rT : Type} [ProbLangℝ rT] (encode : α → Val rT) (xs : List α)
    {k : ℕ} (s : ReservoirLaw.Slots k) : Val rT :=
  listVal id (List.ofFn (entry encode xs ∘ s))

private theorem stream_split {α : Type*} (decode : ℕ → α) (n k : ℕ) (h : k ≤ n) :
    (List.range' 0 n).map decode =
      (List.range' 0 k).map decode ++ (List.range' k (n - k)).map decode := by
  simpa only [List.map_append, Nat.zero_add, Nat.add_sub_of_le h] using
    (congrArg (List.map decode)
      (List.range'_append_1 (s := 0) (m := k) (n := n - k))).symm

private theorem stream_initial {α : Type*} (decode : ℕ → α) (k : ℕ) :
    (List.range' 0 k).map decode = List.ofFn (decode ∘ ReservoirLaw.initial k) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [ReservoirLaw.initial]

private theorem encoded_stream {rT : Type} [ProbLangℝ rT]
    (encode : α → Val rT) (xs : List α) :
    xs.map encode = (List.range' 0 xs.length).map (entry encode xs) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hix : i < xs.length := by simpa only [List.length_map] using hi
    simp [entry, List.getElem?_eq_getElem hix]

private theorem listVal_map {rT : Type} [ProbLangℝ rT]
    (encode : α → Val rT) (xs : List α) : listVal id (xs.map encode) = listVal encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs IH => simp only [List.map_cons, listVal, id_eq, IH]

/-- The closed ordered-slot law, normalized throughout the terminating domain. -/
def law (xs : List α) (k : ℕ) (_hkn : k ≤ xs.length) :=
  ReservoirLaw.law xs.length k

instance (xs : List α) (k : ℕ) (hkn : k ≤ xs.length) :
    MeasureTheory.IsProbabilityMeasure (law xs k hkn) := by
  let : Fact (k ≤ xs.length) := ⟨hkn⟩
  change MeasureTheory.IsProbabilityMeasure (ReservoirLaw.law xs.length k)
  infer_instance

private theorem valid_guard (n k : ℕ) (hkn : k ≤ n) :
    decide ((n : ℤ) < k) = false := decide_eq_false (by omega)

private theorem positive_capacity_guard {rT : Type} [BEq rT] (k : ℕ) (hk : k ≠ 0) :
    ((BaseLit.int (k : ℤ) : BaseLit rT) == .int 0) = false := by
  change ((k : ℤ) == 0) = false
  exact beq_eq_false_iff_ne.mpr (by omega)

private theorem zero_capacity_expectation (n : ℕ) (F : ReservoirLaw.Slots 0 → ℝ≥0∞) :
    (∫⁻ s, F s ∂ReservoirLaw.law n 0) = F (ReservoirLaw.initial 0) := by
  let : Fact (0 ≤ n) := ⟨Nat.zero_le n⟩
  have hF : F = fun _ => F (ReservoirLaw.initial 0) :=
    funext fun s => congrArg F (Subsingleton.elim s _)
  rw [hF]
  simp

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

private theorem twp_scan (E : CoPset) (l : Loc) (decode : ℕ → Val rT)
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

/-- Reservoir Algorithm R, with its exact law on ordered original-position slots. -/
theorem twp_reservoir (E : CoPset) (encode : α → Val rT) (xs : List α)
    (k : ℕ) (hkn : k ≤ xs.length) (F : ReservoirLaw.Slots k → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ s, F s ∂ReservoirLaw.law xs.length k) -∗
      tglWp E pl(&Occil.reservoir &(listVal encode xs).fst #int (k : ℤ))
        (fun v => iprop(∃ s : ReservoirLaw.Slots k,
          ⌜v = output encode xs s⌝ ∗ ↯ (F s))) := by
  iintro Hcredit
  iterate 2 twp_pure
  simp only [ArraySyntax.length_openRec, ArraySyntax.length_closeRec,
    ArraySyntax.readArray_openRec, ArraySyntax.readArray_closeRec,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  twp_bind pl(&Occil.length &(listVal encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E encode xs
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard xs.length k hkn]
  simp only [Bool.or_false]
  twp_pures
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero]
    twp_pures
    twp_value
    imodintro
    iexists ReservoirLaw.initial 0
    isimp only [zero_capacity_expectation] at Hcredit
    iframe Hcredit
    ipureintro
    simp only [output, List.ofFn_zero, listVal]
  · rw [positive_capacity_guard k hk]
    twp_pures
    twp_bind pl(allocN(#int (k : ℤ), #()))
    iapply (twp_allocN (n := (k : ℤ)) (v := Val.unit)
      (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hk)))
    iintro %l Harray
    isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Harray
    iterate 2 twp_pure
    twp_bind pl(&(scan (rT := rT) l k) &(listVal encode xs).fst #0)
    iapply tglWp_wand
    isplitl [Harray Hcredit]
    · rw [← listVal_map encode xs, encoded_stream]
      iapply (twp_scan E l (entry encode xs) xs.length k hkn F) $$ Harray
      rw [ReservoirLaw.finish_bridge hkn]
      iexact Hcredit
    iintro %w ⟨%hw, %s, Harray, Hcredit⟩
    subst w
    twp_pure
    twp_bind pl(&Occil.readArray #loc l #0 #int (k : ℤ))
    iapply tglWp_wand
    isplitl [Harray]
    · have hread := Array.twp_readArray (GF := GF) E l
        (List.ofFn (entry encode xs ∘ s)) 0
      simp only [Nat.cast_zero, add_zero, Nat.zero_add, List.length_ofFn] at hread
      iapply hread $$ Harray
    iintro %v ⟨%hv, Harray⟩
    iapply (tglWp_value (v := v))
    iexists s
    iframe Hcredit
    ipureintro
    exact hv

theorem reservoir_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α)
    (k : ℕ) (hkn : k ≤ xs.length) :
    IsDistSpec (GF := GF) E pl(&Occil.reservoir &(listVal encode xs).fst #int (k : ℤ))
      (law xs k hkn) (output encode xs) where
  spec F _ := wand_entails (twp_reservoir E encode xs k hkn F)

end specification

end

end SampLib.Reservoir
