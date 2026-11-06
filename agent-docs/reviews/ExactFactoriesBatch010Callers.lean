import SampLib.Bernoulli.POverTangent
import SampLib.Bernoulli.ArctanOverPi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview010

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (e f : ℤ) (he : 0 < e) (hef : e < f)
    (hgap : (e : ℝ) / f ≤ Real.sin p - p * Real.cos p)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (POverTangent.pOverTangent_distSpec E p coin hcoin e f he hef hgap) F I

private theorem gap_one : (1 : ℝ) / 5 ≤ Real.sin 1 - Real.cos 1 := by
  have hs : (5 : ℝ) / 6 < Real.sin 1 := by
    have h := Real.sin_gt_sub_cube (x := 1) (by norm_num)
    norm_num at h
    exact h
  have hc : Real.cos 1 < (3 : ℝ) / 5 := by
    nlinarith [Real.sin_sq_add_cos_sq 1, sq_nonneg (Real.sin 1 - 5 / 6),
      sq_nonneg (Real.cos 1 - 3 / 5)]
  linarith

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 1) Val.bool)
    (I : IProp GF) :=
  frame (POverTangent.pOverTangent_distSpec E 1 coin hcoin 1 5
    (by norm_num) (by norm_num) (by simpa using gap_one))
    (fun b => if b then ∞ else 0) I

example : ¬ ((1 : ℝ) / 5 ≤ Real.sin (0 : unitInterval) -
    (0 : unitInterval) * Real.cos (0 : unitInterval)) := by
  norm_num

example (p : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (hgap : (e : ℝ) / f ≤ Real.sin p - p * Real.cos p) :
    (POverTangent.bias p e f he hef hgap : ℝ) = p / Real.tan p :=
  POverTangent.bias_coe p e f he hef hgap

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArctanOverPi.arctanOverPi_distSpec E p coin hcoin) F I

example (E : CoPset) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law 0) Val.bool)
    (I : IProp GF) :=
  frame (ArctanOverPi.arctanOverPi_distSpec E 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example : (ArctanOverPi.bias 0 : ℝ) = 0 := by simp

example : (ArctanOverPi.bias 1 : ℝ) = 1 / 4 := by
  rw [ArctanOverPi.bias_coe]
  simp only [Set.Icc.coe_one, Real.arctan_one]
  field_simp

#print axioms ArctanOverPi.arctanOverPi_distSpec
#print axioms POverTangent.pOverTangent_distSpec
#print axioms POverTangent.bias_coe

end

end ExactFactoriesReview010
