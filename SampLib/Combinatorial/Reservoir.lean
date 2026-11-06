import SampLib.Core.ArrayOwnership
import SampLib.Combinatorial.Support.ReservoirScan
import SampLib.Combinatorial.Choice
import SampLib.Uniform.UniformInt
import SampLib.Core.Syntax.Arrays
import Samplers.Combinatorial.Basic

/-! # Reservoir sampling with the exact law of its ordered slots

The selected position subset is uniform. Retained initial entries keep their
original slots; selected later entries are uniform among the remaining slots.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Reservoir

noncomputable section

/-- Original-position decoding; the fallback lies outside the target law's support. -/
def entry {rT : Type} [ProbLangℝ rT] (encode : α → Val rT) (xs : List α)
    (j : ℕ) : Val rT := ((xs.map encode)[j]?).getD Val.unit

/-- Decode the selected original positions in the reservoir's actual slot order. -/
def output {rT : Type} [ProbLangℝ rT] (encode : α → Val rT) (xs : List α)
    {k : ℕ} (s : ReservoirLaw.Slots k) : Val rT :=
  listVal id (List.ofFn (entry encode xs ∘ s))

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

private theorem valid_guard (n k : ℕ) (hkn : k ≤ n) :
    decide ((n : ℤ) < k) = false := decide_eq_false (by omega)

private theorem positive_capacity_guard {rT : Type} [BEq rT] (k : ℕ) (hk : k ≠ 0) :
    ((BaseLit.int (k : ℤ) : BaseLit rT) == .int 0) = false := by
  change ((k : ℤ) == 0) = false
  exact beq_eq_false_iff_ne.mpr (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

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
