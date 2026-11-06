import SampLib.Discrete.Support.IntegerSqrt

open ProbLang
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

#print axioms SampLib.IntegerSqrt.newton_lower_bound
#print axioms SampLib.IntegerSqrt.newton_terminal
#print axioms SampLib.IntegerSqrt.twp_integerSqrt

section

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (n : ℕ) (R : IProp GF) :
    ⊢ R -∗ tglWp E pl(&Occil.DiscreteExtra.integerSqrt #int (n : ℤ))
      (fun v => iprop(⌜v = Val.int (Nat.sqrt n : ℤ)⌝ ∗ R)) := by
  iintro HR
  iapply tglWp_wand
  isplitl []
  · iapply SampLib.IntegerSqrt.twp_integerSqrt E n
  iintro %v %hv
  iframe HR
  ipureintro
  exact hv

example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.integerSqrt #10)
      (fun v : Val rT => iprop(⌜v = Val.int 3⌝)) := by
  convert SampLib.IntegerSqrt.twp_integerSqrt (rT := rT) (GF := GF) E 10 using 1;
    norm_num

end
