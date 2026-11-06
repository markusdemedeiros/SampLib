import SampLib.Templates
import Samplers.Data
import Metrology.Iris.LocalBI

/-! ProbLang list values and deterministic access specifications. -/

open ProbLang

namespace SampLib

variable {rT : Type _} {α : Type _}

/-- Nil and cons use the sampler library's sum/product representation. -/
def listVal [ProbLangℝ rT] (encode : α → Val rT) : List α → Val rT
  | [] => .inl .unit
  | x :: xs => .inr (.pair (encode x) (listVal encode xs))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The object-language length agrees with the mathematical list length. -/
theorem twp_length (E : CoPset) (encode : α → Val rT) (xs : List α) :
    ⊢ tglWp E pl(&Occil.length &(listVal encode xs).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (xs.length : ℤ)⌝)) := by
  induction xs with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons x xs IH =>
    simp only [listVal]
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_bind pl(&Occil.length &(listVal encode xs).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    simp [add_comm]

/-- In-range object-language lookup returns the corresponding encoded element. -/
theorem twp_getAt (E : CoPset) (encode : α → Val rT) (xs : List α)
    (i : Fin xs.length) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal encode xs).fst #int (i.val : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (xs.get i)⌝)) := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs IH =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [listVal]
      twp_pures
      simp only [List.get_eq_getElem, Fin.val_zero, List.getElem_cons_zero]
      change ⊢ tglWp E (Exp.ofVal (encode x)) (fun v => iprop(⌜v = encode x⌝))
      iapply (tglWp_value (v := encode x))
      itrivial
    · simp only [listVal]
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      twp_pure
      rw [Fin.val_succ, Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.getAt &(listVal encode xs).fst #int (i.val : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      change ⊢ tglWp E pl(&Occil.getAt &(listVal encode xs).fst #int (i.val : ℤ))
        (fun v : Val rT => iprop(⌜v = encode (xs.get i)⌝))
      exact IH i

end specification

end SampLib
