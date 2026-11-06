import SampLib.Combinatorial.SampleWithReplacement
import SampLib.Core.SamplerTerms
import Samplers.General.Core

/-! # Independent uniform character sequences

Characters are list entries; repeated entries retain their position multiplicity.
The law is the independent finite-position product used by replacement sampling.
-/

open ProbLang Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

namespace SampLib.RandomString

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

/-- Independent uniform positions in a nonempty alphabet. -/
theorem randomString_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.randomString &(listVal encode xs).fst #int (n : ℤ))
      (SampleWithReplacement.law (Choice.law xs.length) n)
      (fun ys => listVal (fun i => encode (xs.get i)) (List.ofFn ys)) where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [SamplerTerms.sampleWithReplacement_openRec,
      SamplerTerms.sampleWithReplacement_closeRec]
    iapply (SampleWithReplacement.sampleWithReplacement_distSpec E encode xs n).spec
      F hF $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
/-- The empty string requires no randomness, even over an empty alphabet. -/
theorem randomString_zero_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.randomString &(listVal encode xs).fst #int (0 : ℤ))
      (MeasureTheory.Measure.dirac ()) (fun _ : Unit => listVal encode []) where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [SamplerTerms.sampleWithReplacement_openRec,
      SamplerTerms.sampleWithReplacement_closeRec]
    iapply (SampleWithReplacement.sampleWithReplacement_zero_distSpec E encode xs).spec
      F hF $$ Hcredit

end

end SampLib.RandomString
