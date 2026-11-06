import SampLib.Samplers.LogPiOverPi
import SampLib.Samplers.ArctanRationalOverRatio
import SampLib.Samplers.InverseSqrtPi
import SampLib.Samplers.BinaryExponential

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview008

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

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (LogPiOverPi.logPiOverPi_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (LogPiOverPi.logPiOverPi_distSpec E) (fun b => if b then ∞ else 0) I

example : (LogPiOverPi.bias : ℝ) = Real.log Real.pi / Real.pi := LogPiOverPi.bias_coe

example (E : CoPset) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≤ y)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ArctanRationalOverRatio.arctanRationalOverRatio_distSpec E x y hx hy hxy) F I

example (E : CoPset) (I : IProp GF) :=
  frame (ArctanRationalOverRatio.arctanRationalOverRatio_distSpec E 0 7
    (by norm_num) (by norm_num) (by norm_num)) (fun b => if b then 0 else ∞) I

example (E : CoPset) (I : IProp GF) :=
  frame (ArctanRationalOverRatio.arctanRationalOverRatio_distSpec E 7 7
    (by norm_num) (by norm_num) (by norm_num)) (fun b => if b then ∞ else 0) I

example : (ArctanRationalOverRatio.bias 0 7
    (by norm_num) (by norm_num) (by norm_num) : ℝ) = 1 := by
  rw [ArctanRationalOverRatio.bias_zero]
  rfl

example : (ArctanRationalOverRatio.bias 7 7
    (by norm_num) (by norm_num) (by norm_num) : ℝ) = Real.pi / 4 := by
  rw [ArctanRationalOverRatio.bias_coe 7 7 (by norm_num)]
  norm_num [Real.arctan_one]

example (E : CoPset) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (InverseSqrtPi.inverseSqrtPi_distSpec E) F I

example (E : CoPset) (I : IProp GF) :=
  frame (InverseSqrtPi.inverseSqrtPi_distSpec E) (fun b => if b then 0 else ∞) I

example : (InverseSqrtPi.bias : ℝ) = 1 / Real.sqrt Real.pi := InverseSqrtPi.bias_coe

example (E : CoPset) (p : unitInterval) (m k : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (BinaryExponential.binaryExponential_distSpec E p m k coin hcoin) F I

example (E : CoPset) (p : unitInterval) (k : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (I : IProp GF) :=
  frame (BinaryExponential.binaryExponential_distSpec E p 0 k coin hcoin)
    (fun b => if b then 0 else ∞) I

example (E : CoPset) (p : unitInterval) (m : ℕ) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (I : IProp GF) :=
  frame (BinaryExponential.binaryExponential_distSpec E p m 0 coin hcoin)
    (fun b => if b then ∞ else 0) I

example (p : unitInterval) (k : ℕ) : (BinaryExponential.bias p 0 k : ℝ) = 1 := by
  rw [BinaryExponential.bias_coe]
  simp

example : (BinaryExponential.bias 0 1 1 : ℝ) = 1 / 2 := by
  rw [BinaryExponential.bias_coe]
  norm_num [Real.rpow_neg]

#print axioms LogPiOverPi.logPiOverPi_distSpec
#print axioms LogPiOverPi.twp_logPiOverPi
#print axioms ArctanRationalOverRatio.arctanRationalOverRatio_distSpec
#print axioms InverseSqrtPi.inverseSqrtPi_distSpec
#print axioms BinaryExponential.binaryExponential_distSpec

end

end ExactFactoriesReview008
