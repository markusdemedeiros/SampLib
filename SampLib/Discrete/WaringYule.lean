import SampLib.Discrete.BetaNegativeBinomial
import SampLib.Discrete.Support.BetaNegativeBinomialSyntax

/-! # Waring–Yule waiting counts as a beta-geometric law -/

open ProbLang
open scoped ENNReal

namespace SampLib.WaringYule

noncomputable section

abbrev law (D : BetaNegativeBinomial.Parameters) := BetaNegativeBinomial.law D 1

/-- The one-success specialization of the beta-negative-binomial mass function. -/
theorem mass (D : BetaNegativeBinomial.Parameters) (n : ℕ) :
    law D {n} = InverseUrn.positiveMass 0 (BetaNegativeBinomial.marked D)
      (BetaNegativeBinomial.unmarked D) (BetaNegativeBinomial.reinforcement D) n :=
  BetaNegativeBinomial.mass D 0 n

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem waringYule_distSpec (E : CoPset) (D : BetaNegativeBinomial.Parameters) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.waringYule #int (D.alphaNumerator : ℤ)
        #int (D.alphaDenominator : ℤ) #int (D.betaNumerator : ℤ) #int (D.betaDenominator : ℤ))
      (law D) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F hF := by
    iintro Hcredit
    iterate 4 twp_pure
    simp only [BetaNegativeBinomial.betaNegativeBinomial_openRec,
      BetaNegativeBinomial.betaNegativeBinomial_closeRec]
    have h := BetaNegativeBinomial.betaNegativeBinomial_distSpec (rT := rT) (GF := GF) E D 1
    simp only [Nat.cast_one] at h
    isimp only [law] at Hcredit
    iapply h.spec F hF $$ Hcredit

end specification

end

end SampLib.WaringYule
