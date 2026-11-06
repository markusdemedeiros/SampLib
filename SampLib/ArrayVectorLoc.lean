import SampLib.ArrayVector

/-! # A vector write after the address has been evaluated -/

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

namespace SampLib.Array

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The ordinary array lens, with the already evaluated indexed location. -/
theorem twp_store_vector_loc (E : CoPset) (l : Loc) {n : ℕ} {α : Type}
    (encode : α → Val rT) (a : Fin n → α) (i : Fin n) (x : α) :
    owns l (List.ofFn (encode ∘ a)) ⊢
      tglWp E (Exp.store pl(#loc (l + (i.val : ℤ))) (Exp.ofVal (encode x)))
        (fun v => iprop(⌜v = Val.unit⌝ ∗
          owns l (List.ofFn (encode ∘ Function.update a i x)))) := by
  iintro Harray
  ihave ⟨Hi, Hrestore⟩ := access l (List.ofFn (encode ∘ a))
    ⟨i.val, by simp⟩ $$ Harray
  iapply twp_store
  iframe Hi
  iintro Hi
  ihave Harray := Hrestore $$ %(encode x) Hi
  isimp only [Function.comp_update, Permutations.ofFn_update]
  iframe Harray

end SampLib.Array
