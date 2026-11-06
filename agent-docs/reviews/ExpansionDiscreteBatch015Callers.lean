import SampLib.Weighted.CumulativeChoice
import SampLib.Weighted.RationalChoice

/-! Public clients for metadata-only derived-classification corrections. -/

open ProbLang Iris TotalEris ErisWpGS SampLib

namespace ExpansionDiscreteCorrection

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

example (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.Weighted.cumulativeChoice
      &(listVal (fun n : ℕ => Val.int n) ws).fst #())
      (SampLib.CategoricalCDF.law ws) Val.int :=
  SampLib.CumulativeChoice.cumulativeChoice_distSpec E ws

example (E : CoPset) (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < SampLib.RationalChoice.numerators ws) :
    SampLib.IsDistSpec (GF := GF) E pl(&Occil.Weighted.rationalChoice
      &(listVal SampLib.RationalChoice.fractionVal ws).fst #())
      (SampLib.RationalChoice.law ws hden hs) (fun i : ℕ => Val.int (i : ℤ)) :=
  SampLib.RationalChoice.rationalChoice_distSpec E ws hden hs

#print axioms SampLib.CumulativeChoice.cumulativeChoice_distSpec
#print axioms SampLib.RationalChoice.rationalChoice_distSpec

end

end ExpansionDiscreteCorrection
