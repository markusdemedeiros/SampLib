import SampLib.Combinatorial.SampleWithReplacement
import SampLib.Core.ListOperations
import SampLib.Common.Syntax.Shuffle
import Samplers.General.DataModels

/-! # Independent permutation resamples

Each replicate uses a fresh uniform position permutation of the observations.
Equal observations retain their separate positional multiplicities.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PermutationSamples

noncomputable section

abbrev law {α : Type _} (xs : List α) (n : ℕ) :=
  SampleWithReplacement.law (Shuffle.law xs) n

private def sampler {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (xs : List α) : Val rT :=
  ⟨.lam (.app Occil.shuffle (listVal encode xs).fst), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

private theorem sampler_spec (E : CoPset) (encode : α → Val rT) (xs : List α) :
    IsDistSpec (GF := GF) E pl(&(sampler encode xs).fst #())
      (Shuffle.law xs) (fun σ => listVal encode (Shuffle.output xs σ)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [Shuffle.shuffle_openRec]
    iapply (Shuffle.shuffle_distSpec E encode xs).spec F hF $$ Hcredit

/-- Every nonnegative replicate count, including empty data and zero replicates. -/
theorem permutationSamples_distSpec (E : CoPset) (encode : α → Val rT)
    (xs : List α) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.permutationSamples &(listVal encode xs).fst #int (n : ℤ) #())
      (law xs n) (fun ys => listVal
        (fun σ => listVal encode (Shuffle.output xs σ)) (List.ofFn ys)) where
  spec F hF := by
    iintro Hcredit
    iterate 5 twp_pure
    simp only [Shuffle.shuffle_openRec, Shuffle.shuffle_closeRec,
      ListOperations.repeatSample_openRec, ListOperations.repeatSample_closeRec]
    twp_bind pl(&Occil.repeatSample &(sampler encode xs).fst #int (n : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (SampleWithReplacement.repeatSample_distSpec E (Shuffle.law xs)
      (fun σ => listVal encode (Shuffle.output xs σ)) (sampler encode xs)
      (sampler_spec E encode xs) n).spec F hF $$ Hcredit

end specification

end

end SampLib.PermutationSamples
