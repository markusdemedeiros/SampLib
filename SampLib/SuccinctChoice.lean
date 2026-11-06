import SampLib.Distributions.PackedWeights
import SampLib.Distributions.WeightMaximum
import SampLib.Syntax.SuccinctChoice
import SampLib.KnownIntegerComparison

/-! # Deterministic preparation of packed categorical weights -/

open ProbLang

namespace SampLib.SuccinctChoice

private theorem predecessor_cast (i : ℕ) : ((i + 1 : ℕ) : ℤ) - 1 = (i : ℤ) := by omega

private theorem order_test (current w : ℕ) :
    decide ((current : ℤ) < w) = decide (current < w) := by
  apply decide_eq_decide.mpr
  exact_mod_cast Iff.rfl

private theorem word_test (w : ℕ) (hw : w < 2 ^ 32) :
    decide ((2 : ℤ) ^ 32 ≤ w) = false :=
  decide_eq_false (by exact_mod_cast not_le.mpr hw)

private theorem wide_test (w : ℕ) :
    decide ((2 : ℤ) ^ 20 ≤ w) = decide (PackedWeights.Wide w) := by
  apply decide_eq_decide.mpr
  change (2 : ℤ) ^ 20 ≤ w ↔ 2 ^ 20 ≤ w
  norm_cast

private theorem bits_accumulator (w : ℕ) (ws : List ℕ) (offset : ℕ) (accumulator : ℤ) :
    accumulator + (2 : ℤ) ^ offset * (PackedWeights.bits (w :: ws) : ℤ) =
      (accumulator + (w : ℤ) * 2 ^ offset) +
        2 ^ (offset + PackedWeights.width w) * (PackedWeights.bits ws : ℤ) := by
  simp only [PackedWeights.bits_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, pow_add]
  ring

private theorem mask_accumulator (w : ℕ) (ws : List ℕ) (index : ℕ) (accumulator : ℤ) :
    accumulator + (2 : ℤ) ^ index * (PackedWeights.mask (w :: ws) : ℤ) =
      (accumulator + (PackedWeights.flag w : ℤ) * 2 ^ index) +
        2 ^ (index + 1) * (PackedWeights.mask ws : ℤ) := by
  simp only [PackedWeights.mask_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  ring

abbrev packVal {rT : Type} (index offset : ℕ) (bits shorts : ℤ) (ws : List ℕ) : Val rT :=
  .pair (.int (bits + (2 : ℤ) ^ offset * (PackedWeights.bits ws : ℤ)))
    (.int (shorts + (2 : ℤ) ^ index * (PackedWeights.mask ws : ℤ)))

private theorem packVal_step {rT : Type} (w : ℕ) (ws : List ℕ) (index offset chosen : ℕ)
    (bits shorts newMask : ℤ) (hwidth : chosen = PackedWeights.width w)
    (hmask : newMask = shorts + (PackedWeights.flag w : ℤ) * 2 ^ index) :
    (packVal (index + 1) (offset + chosen) (bits + (w : ℤ) * 2 ^ offset) newMask ws : Val rT) =
      packVal index offset bits shorts (w :: ws) := by
  rw [hwidth, hmask]
  unfold packVal
  rw [← bits_accumulator, ← mask_accumulator]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.SuccinctChoice.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The source's limited population count agrees with its natural-number recurrence. -/
theorem twp_count (E : CoPset) (i bits : ℕ) :
    ⊢ tglWp E pl(&Program.count #int (i : ℤ) #int (bits : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (PackedBits.count i bits : ℤ)⌝)) := by
  induction i generalizing bits with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | succ i ih =>
    iterate 7 twp_pure
    rw [predecessor_cast i]
    isimp only [Exp.ofVal]
    twp_bind pl(&Program.count #int (i : ℤ) #int ((bits / 2 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply ih (bits / 2)
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply congrArg Val.int
    simp only [PackedBits.count, Nat.cast_add, Int.natCast_emod, Nat.cast_ofNat]

/-- The running-max source constructs a valid rejection envelope. -/
theorem twp_maximum (E : CoPset) (ws : List ℕ) (current : ℕ) :
    ⊢ tglWp E pl(&Program.maximum
      &(listVal (fun n : ℕ => Val.int n) ws).fst #int (current : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (WeightMaximum.maximum ws current : ℤ)⌝)) := by
  induction ws generalizing current with
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
    rw [order_test current w]
    by_cases h : current < w
    · rw [decide_eq_true h]
      iterate 3 twp_pure
      isimp only [WeightMaximum.maximum_cons, max_eq_right h.le, Exp.ofVal]
      iapply ih w
    · rw [decide_eq_false h]
      iterate 2 twp_pure
      isimp only [WeightMaximum.maximum_cons, max_eq_left (Nat.le_of_not_gt h), Exp.ofVal]
      iapply ih current

private theorem twp_pack_finish (E : CoPset) (w : ℕ) (ws : List ℕ) (index offset chosen : ℕ)
    (bits shorts newMask : ℤ) (hwidth : chosen = PackedWeights.width w)
    (hmask : newMask = shorts + (PackedWeights.flag w : ℤ) * 2 ^ index)
    (hrec : ⊢ tglWp E pl(&Program.pack &(listVal (fun n : ℕ => Val.int n) ws).fst
      #int ((index + 1 : ℕ) : ℤ) #int ((offset + chosen : ℕ) : ℤ)
      #int (bits + (w : ℤ) * 2 ^ offset) #int newMask)
      (fun v : Val rT => iprop(⌜v = packVal (index + 1) (offset + chosen)
        (bits + (w : ℤ) * 2 ^ offset) newMask ws⌝))) :
    ⊢ tglWp E (Program.finishPack ws w index offset chosen bits newMask)
      (fun v : Val rT => iprop(⌜v = packVal index offset bits shorts (w :: ws)⌝)) := by
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (offset : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower E 2 offset
  iintro %v %hv
  subst v
  iterate 5 twp_pure
  rw [← Nat.cast_add_one, ← Nat.cast_add offset chosen]
  isimp only [Exp.ofVal]
  iapply tglWp_wand
  isplitl []
  · iapply hrec
  iintro %v %hv
  subst v
  ipureintro
  exact packVal_step w ws index offset chosen bits shorts newMask hwidth hmask

/-- Packing implements exact mixed-width concatenation and its parallel binary flag mask. -/
theorem twp_pack (E : CoPset) (ws : List ℕ) (hfit : ∀ w ∈ ws, w < 2 ^ 32)
    (index offset : ℕ) (bits shorts : ℤ) :
    ⊢ tglWp E pl(&Program.pack &(listVal (fun n : ℕ => Val.int n) ws).fst
      #int (index : ℤ) #int (offset : ℤ) #int bits #int shorts)
      (fun v : Val rT => iprop(⌜v = packVal index offset bits shorts ws⌝)) := by
  induction ws generalizing index offset bits shorts with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [packVal, PackedWeights.bits, PackedWeights.mask, PackedWeights.flags,
      PackedBits.encode, List.map_nil, Nat.cast_zero, mul_zero, add_zero]
  | cons w ws ih =>
    have hw := hfit w (by simp)
    have ht : ∀ x ∈ ws, x < 2 ^ 32 := fun x hx => hfit x (by simp [hx])
    simp only [listVal]
    iterate 10 twp_pure
    twp_bind pl(&Occil.Weighted.integerPower #2 #32)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedIntegerPower.twp_integerPower E 2 32
    iintro %v %hv
    subst v
    twp_bind pl(#int ((2 : ℤ) ^ 32) <= #int (w : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply KnownIntegerComparison.twp_le E (2 ^ 32) w false (word_test w hw)
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.Weighted.integerPower #2 #20)
    iapply tglWp_wand
    isplitl []
    · iapply WeightedIntegerPower.twp_integerPower E 2 20
    iintro %v %hv
    subst v
    twp_bind pl(#int ((2 : ℤ) ^ 20) <= #int (w : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply KnownIntegerComparison.twp_le E (2 ^ 20) w
        (decide (PackedWeights.Wide w)) (wide_test w)
    iintro %v %hv
    subst v
    by_cases h : PackedWeights.Wide w
    · rw [decide_eq_true h]
      iterate 4 twp_pure
      twp_bind pl(&Occil.Weighted.integerPower #2 #int (index : ℤ))
      iapply tglWp_wand
      isplitl []
      · iapply WeightedIntegerPower.twp_integerPower E 2 index
      iintro %v %hv
      subst v
      iterate 2 twp_pure
      iapply twp_pack_finish E w ws index offset 32 bits shorts (shorts + 2 ^ index)
        (by simp [PackedWeights.width, h]) (by simp [PackedWeights.flag, h])
        (ih ht (index + 1) (offset + 32) (bits + (w : ℤ) * 2 ^ offset) (shorts + 2 ^ index))
    · rw [decide_eq_false h]
      iterate 5 twp_pure
      iapply twp_pack_finish E w ws index offset 20 bits shorts shorts
        (by simp [PackedWeights.width, h]) (by simp [PackedWeights.flag, h])
        (ih ht (index + 1) (offset + 20) (bits + (w : ℤ) * 2 ^ offset) shorts)

end specification

end SampLib.SuccinctChoice
