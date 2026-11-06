import SampLib.Core.DistributionMap
import SampLib.Common.Syntax.Shuffle

/-! Fisher–Yates specifications for vectors indexed by a prescribed finite type. -/

open ProbLang Equiv
open scoped ENNReal

namespace SampLib.Shuffle

noncomputable section

private def reindex {m n : ℕ} (h : m = n) : Perm (Fin m) ≃ Perm (Fin n) :=
  (finCongr h).permCongr

private theorem reindex_law {m n : ℕ} (h : m = n) :
    (Permutations.law m).map (reindex h) = Permutations.law n := by
  subst n
  have he : (reindex (rfl : m = m) : Perm (Fin m) → Perm (Fin m)) = id := by
    funext σ
    ext i
    rfl
  rw [he, MeasureTheory.Measure.map_id]

private theorem vector_output {rT : Type} [ProbLangℝ rT] (encode : α → Val rT)
    {n : ℕ} (a : Fin n → α) (σ : Perm (Fin (List.ofFn a).length)) :
    listVal encode (output (List.ofFn a) σ) =
      listVal encode (List.ofFn (a ∘ reindex List.length_ofFn σ)) := by
  congr 1
  apply List.ext_getElem
  · simp only [output, List.length_ofFn]
  · intro i hi hi'
    simp [output, List.get_eq_getElem, reindex, Equiv.permCongr_apply,
      finCongr, Function.comp_def]
    exact congrArg a (Fin.ext rfl)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- Reindex the latent positions without changing the sampled list. -/
theorem shuffleVector_distSpec (E : CoPset) (encode : α → Val rT)
    {n : ℕ} (a : Fin n → α) :
    IsDistSpec (GF := GF) E pl(&Occil.shuffle &(listVal encode (List.ofFn a)).fst)
      (Permutations.law n) (fun σ => listVal encode (List.ofFn (a ∘ σ))) := by
  have hs := (shuffle_distSpec (GF := GF) E encode (List.ofFn a)).map
    (reindex List.length_ofFn) (measurable_of_countable _)
    (fun σ => listVal encode (List.ofFn (a ∘ σ))) (vector_output encode a)
  simp only [law, reindex_law] at hs
  exact hs

end specification

end

end SampLib.Shuffle
