import SampLib.General.Laws.RandomMapSupport
import SampLib.General.RandomMap
import SampLib.General.CFTPDeterministic
import SampLib.Core.DistributionMapSupported

/-! # A typed interface to the existing random-map sampler

The almost-sure valid-list support makes its integer-list encoding exactly the
finite-function encoding required by CFTP.
-/

open ProbLang

namespace SampLib.RandomMapSupport

noncomputable section

open CouplingFromPast

private theorem listVal_map {rT α β : Type _} [ProbLangℝ rT]
    (encode : β → Val rT) (f : α → β) (xs : List α) :
    listVal encode (xs.map f) = listVal (fun x => encode (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs IH => simp only [List.map_cons, listVal, IH]

/-- On valid lists, decoding and re-encoding preserves the actual runtime value. -/
theorem mapVal_decode {rT : Type _} [ProbLangℝ rT] (n : ℕ) [NeZero n]
    (xs : List ℕ) (hxs : Valid n xs) :
    mapVal (rT := rT) (decode n xs) = listVal (fun j : ℕ => Val.int (j : ℤ)) xs := by
  calc
    _ = listVal (fun j : ℕ => Val.int (j : ℤ)) ((List.ofFn (decode n xs)).map Fin.val) := by
      rw [listVal_map]
      rfl
    _ = _ := by
      simpa only [List.map_ofFn, Function.comp_def] using
        congrArg (listVal (fun j : ℕ => Val.int (j : ℤ))) (decode_list n xs hxs)

section specification

open Iris ProbLang.TotalEris

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- The original program samples exactly the typed random-mapping law. -/
theorem typedRandomMap_distSpec (E : CoPset) (rows : List Row) [NeZero rows.length]
    (hsquare : ∀ r ∈ rows, r.val.length = rows.length) :
    IsDistSpec (GF := GF) E pl(&Occil.General.randomMap
      &(listVal RandomMap.encodeRow rows).fst #()) (law rows) mapVal := by
  have h := (RandomMap.randomMap_distSpec (GF := GF) E rows).map_supported
    (Valid rows.length) (Set.to_countable _).measurableSet
    (valid_ae rows rows.length hsquare)
    (decode rows.length) (measurable_of_countable _) mapVal
    (fun xs hxs => (mapVal_decode rows.length xs hxs).symm)
  simpa only [law] using h

end specification

end

end SampLib.RandomMapSupport
