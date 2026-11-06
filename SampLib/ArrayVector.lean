import SampLib.ArrayOwnership
import SampLib.Distributions.Permutations

/-! # Array lenses for mathematical vectors -/

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

namespace SampLib.Array

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Writing an encoded vector entry corresponds to a single mathematical update. -/
theorem twp_store_vector (E : CoPset) (l : Loc) {n : ℕ} {α : Type*}
    (encode : α → Val rT) (a : Fin n → α) (i : Fin n) (x : α) :
    owns l (List.ofFn (encode ∘ a)) ⊢
      tglWp E pl((#loc l +ₗ #int (i.val : ℤ)) ← &(encode x).fst)
        (fun w => iprop(⌜w = Val.unit⌝ ∗ owns l (List.ofFn (encode ∘ Function.update a i x)))) := by
  have h := twp_store_ofFn (GF := GF) E l (encode ∘ a) i (encode x)
  simpa only [Function.comp_update, Permutations.ofFn_update] using h

end SampLib.Array
