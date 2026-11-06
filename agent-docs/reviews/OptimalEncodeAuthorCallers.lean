import SampLib.OptimalEncode

open ProbLang

namespace OptimalEncodeAuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (k l : ℕ) (hl : l < k) (ws : List ℕ) (R : IProp GF) :
    R ⊢ tglWp E pl(&(Optimal.Program.encode k l (OptimalEncoding.denominator k l))
      &(Optimal.listValNatInts ws).fst)
      (fun v : Val rT => iprop(⌜v = Optimal.listValNatInts
        (ws.map (OptimalEncoding.binary k l))⌝ ∗ R)) := by
  iintro HR
  iapply tglWp_wand
  isplitl []
  · iapply Optimal.twp_encode E k l hl ws
  iintro %v %hv
  iframe HR
  ipureintro
  exact hv

example (E : CoPset) (r : ℕ) (ws : List ℕ) :
    ⊢ tglWp E pl(&(Optimal.Program.append r) &(Optimal.listValNatInts ws).fst)
      (fun v : Val rT => iprop(⌜v = Optimal.listValNatInts (ws ++ [r])⌝)) :=
  Optimal.twp_append E r ws

example (E : CoPset) :
    ⊢ tglWp E pl(&(Optimal.Program.encode 3 1 6) &(Optimal.listValNatInts [0, 6, 7]).fst)
      (fun v : Val rT => iprop(⌜v = Optimal.listValNatInts [0, 7, 9]⌝)) := by
  have hm : [0, 6, 7].map (OptimalEncoding.binary 3 1) = [0, 7, 9] := by decide
  have h := Optimal.twp_encode (rT := rT) (GF := GF) E 3 1 (by decide) [0, 6, 7]
  have hD : OptimalEncoding.denominator 3 1 = 6 := by decide
  simpa only [hm, hD] using h

example (E : CoPset) :
    ⊢ tglWp E pl(&(Optimal.Program.encode 3 0 7) &(Optimal.listValNatInts [0, 7, 8]).fst)
      (fun v : Val rT => iprop(⌜v = Optimal.listValNatInts [0, 7, 8]⌝)) := by
  have hm : [0, 7, 8].map (OptimalEncoding.binary 3 0) = [0, 7, 8] := by decide
  have h := Optimal.twp_encode (rT := rT) (GF := GF) E 3 0 (by decide) [0, 7, 8]
  have hD : OptimalEncoding.denominator 3 0 = 7 := by decide
  simpa only [hm, hD] using h

end

end OptimalEncodeAuthorCallers

#print axioms SampLib.Optimal.twp_append
#print axioms SampLib.Optimal.twp_encode
