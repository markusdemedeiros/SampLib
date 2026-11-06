import SampLib.Distributions.AlgebraicConstants
import SampLib.Samplers.IntegerSign

/-! # The square-root-of-two-minus-one coin -/

open ProbLang
open scoped ENNReal

namespace SampLib.SqrtTwoMinusOne

noncomputable section

abbrev bias := AlgebraicConstants.sqrtTwoMinusOneBias

/-- Factoring the quadratic identifies its unique sign-changing root. -/
theorem polynomial_sign (n den : ℕ) (hd : 0 < den) :
    ((n : ℤ) * n + 2 * (n : ℤ) * den - (den : ℤ) * den).sign =
      AlgebraicRoot.side bias (-1) n den := by
  apply IntegerSign.sign_of_right_factor bias n den _ ((n : ℝ) + (bias : ℝ) * den + 2 * den)
  · have hp := AlgebraicConstants.sqrtTwoMinusOneBias_pos
    have hden : (0 : ℝ) < den := by exact_mod_cast hd
    positivity
  · push_cast
    calc
      _ = (n : ℝ) ^ 2 + 2 * n * den -
          ((bias : ℝ) ^ 2 + 2 * (bias : ℝ)) * (den : ℝ) ^ 2 := by
        rw [AlgebraicConstants.sqrtTwoMinusOneBias_equation]
        ring
      _ = _ := by ring

private def oracle {rT : Type _} : Val rT :=
  ⟨pl(fun n d, &Occil.Constants.integerSign (n * n + #2 * n * d - d * d)),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_oracle (E : CoPset) (n den : ℕ) (hd : 0 < den) :
    ⊢ tglWp E pl(&(oracle (rT := rT)).fst #int (n : ℤ) #int (den : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (AlgebraicRoot.side bias (-1) n den)⌝)) := by
  iterate 2 twp_pure
  simp only [IntegerSign.integerSign_closeRec, IntegerSign.integerSign_openRec]
  iterate 6 twp_pure
  iapply tglWp_wand
  isplitl []
  · iapply IntegerSign.twp_integerSign E _
  iintro %v %hv
  ipureintro
  simpa only [polynomial_sign n den hd] using hv

/-- Symbolic execution delegates the sign comparison to the root engine. -/
theorem twp_sqrtTwoMinusOne (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit bias F) -∗ tglWp E pl(&Occil.Constants.sqrtTwoMinusOne #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hroot := AlgebraicRoot.twp_algebraicRoot (rT := rT) (GF := GF) E bias
    AlgebraicConstants.sqrtTwoMinusOneBias_pos AlgebraicConstants.sqrtTwoMinusOneBias_lt_one
    (-1) (Or.inr rfl) oracle (fun n den _ hd => twp_oracle E n den hd) F
  simp [oracle, Exp.close, Exp.closeRec] at hroot
  iintro Hcredit
  twp_pure
  simp only [AlgebraicRoot.algebraicRoot_closeRec, AlgebraicRoot.algebraicRoot_openRec,
    IntegerSign.integerSign_closeRec, IntegerSign.integerSign_openRec]
  iapply hroot $$ Hcredit

/-- Bernoulli at `sqrt 2 - 1`. -/
theorem sqrtTwoMinusOne_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.sqrtTwoMinusOne #())
      (RealCoin.law bias) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails (twp_sqrtTwoMinusOne E F)

end specification

end

end SampLib.SqrtTwoMinusOne
