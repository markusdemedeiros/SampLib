import SampLib.Distributions.AlgebraicConstants
import SampLib.Samplers.IntegerSign

/-! # The inverse-square-root-of-two coin -/

open ProbLang
open scoped ENNReal

namespace SampLib.InverseSqrtTwo

noncomputable section

abbrev bias := AlgebraicConstants.inverseSqrtTwoBias

/-- Factoring the quadratic identifies its positive sign-changing root. -/
theorem polynomial_sign (n den : ℕ) (hd : 0 < den) :
    (2 * (n : ℤ) * n - (den : ℤ) * den).sign =
      AlgebraicRoot.side bias (-1) n den := by
  apply IntegerSign.sign_of_right_factor bias n den _ (2 * ((n : ℝ) + (bias : ℝ) * den))
  · have hp := AlgebraicConstants.inverseSqrtTwoBias_pos
    have hden : (0 : ℝ) < den := by exact_mod_cast hd
    positivity
  · push_cast
    calc
      _ = 2 * (n : ℝ) ^ 2 - (2 * (bias : ℝ) ^ 2) * (den : ℝ) ^ 2 := by
        rw [AlgebraicConstants.inverseSqrtTwoBias_equation]
        ring
      _ = _ := by ring

private def oracle {rT : Type _} : Val rT :=
  ⟨pl(fun n d, &Occil.Constants.integerSign (#2 * n * n - d * d)),
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
  iterate 4 twp_pure
  iapply tglWp_wand
  isplitl []
  · iapply IntegerSign.twp_integerSign E _
  iintro %v %hv
  ipureintro
  simpa only [polynomial_sign n den hd] using hv

/-- Symbolic execution delegates the sign comparison to the root engine. -/
theorem twp_inverseSqrtTwo (E : CoPset) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit bias F) -∗ tglWp E pl(&Occil.Constants.inverseSqrtTwo #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hroot := AlgebraicRoot.twp_algebraicRoot (rT := rT) (GF := GF) E bias
    AlgebraicConstants.inverseSqrtTwoBias_pos AlgebraicConstants.inverseSqrtTwoBias_lt_one
    (-1) (Or.inr rfl) oracle (fun n den _ hd => twp_oracle E n den hd) F
  simp [oracle, Exp.close, Exp.closeRec] at hroot
  iintro Hcredit
  twp_pure
  simp only [AlgebraicRoot.algebraicRoot_closeRec, AlgebraicRoot.algebraicRoot_openRec,
    IntegerSign.integerSign_closeRec, IntegerSign.integerSign_openRec]
  iapply hroot $$ Hcredit

/-- Bernoulli at `1 / sqrt 2`. -/
theorem inverseSqrtTwo_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.inverseSqrtTwo #())
      (RealCoin.law bias) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails (twp_inverseSqrtTwo E F)

end specification

end

end SampLib.InverseSqrtTwo
