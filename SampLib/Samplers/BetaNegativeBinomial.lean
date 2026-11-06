import SampLib.Samplers.InversePolya
import SampLib.Distributions.InverseUrnMass
import SampLib.InversePolyaSyntax

/-! # Beta-negative-binomial counts with positive rational beta shapes

Clearing the two shape denominators produces the reinforced urn. Its canonical
rising-product mass identifies the resulting beta-negative-binomial distribution.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.BetaNegativeBinomial

noncomputable section

/-- Positive rational alpha and beta, passed as unreduced numerator/denominator pairs. -/
structure Parameters where
  alphaNumerator : ℕ
  alphaDenominator : ℕ
  betaNumerator : ℕ
  betaDenominator : ℕ
  alphaNumerator_pos : 0 < alphaNumerator
  alphaDenominator_pos : 0 < alphaDenominator
  betaNumerator_pos : 0 < betaNumerator
  betaDenominator_pos : 0 < betaDenominator

def marked (D : Parameters) : ℕ := D.alphaNumerator * D.betaDenominator

def unmarked (D : Parameters) : ℕ := D.betaNumerator * D.alphaDenominator

def reinforcement (D : Parameters) : ℕ := D.alphaDenominator * D.betaDenominator

private theorem marked_pos (D : Parameters) : 0 < marked D :=
  Nat.mul_pos D.alphaNumerator_pos D.betaDenominator_pos

/-- Failures before `r` successes, with beta shapes alpha and beta. -/
abbrev law (D : Parameters) (r : ℕ) :=
  InversePolya.law r (marked D) (unmarked D) (reinforcement D) (marked_pos D)

/-- For positive success count, the law has the standard rising-product mass. -/
theorem mass (D : Parameters) (r n : ℕ) :
    law D (r + 1) {n} =
      InverseUrn.positiveMass r (marked D) (unmarked D) (reinforcement D) n :=
  InverseUrn.mass_positive r _ _ _ n (marked_pos D)

private theorem valid_test (D : Parameters) :
    Bool.or (Bool.or (Bool.or (decide ((D.alphaNumerator : ℤ) ≤ 0))
      (decide ((D.alphaDenominator : ℤ) ≤ 0)))
      (decide ((D.betaNumerator : ℤ) ≤ 0))) (decide ((D.betaDenominator : ℤ) ≤ 0)) = false := by
  have ha : decide ((D.alphaNumerator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.alphaNumerator_pos.not_ge)
  have hd : decide ((D.alphaDenominator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.alphaDenominator_pos.not_ge)
  have hb : decide ((D.betaNumerator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.betaNumerator_pos.not_ge)
  have he : decide ((D.betaDenominator : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast D.betaDenominator_pos.not_ge)
  rw [ha, hd, hb, he]
  rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Clear the rational shape denominators, then use the verified inverse urn. -/
theorem betaNegativeBinomial_distSpec (E : CoPset) (D : Parameters) (r : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.betaNegativeBinomial #int (r : ℤ)
        #int (D.alphaNumerator : ℤ) #int (D.alphaDenominator : ℤ)
        #int (D.betaNumerator : ℤ) #int (D.betaDenominator : ℤ))
      (law D r) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F hF := by
    iintro Hcredit
    twp_pures
    rw [valid_test D]
    iterate 4 twp_pure
    simp only [InversePolya.inversePolya_openRec, InversePolya.inversePolya_closeRec]
    rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]
    isimp only [Exp.ofVal]
    have h := (InversePolya.inversePolya_distSpec (rT := rT) (GF := GF) E r (marked D) (unmarked D)
      (reinforcement D) (marked_pos D)).spec F hF
    simp only [marked, unmarked, reinforcement] at h
    isimp only [law, marked, unmarked, reinforcement] at Hcredit
    iapply h $$ Hcredit

end specification

end

end SampLib.BetaNegativeBinomial
