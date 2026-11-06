import SampLib.Bernoulli.ExpMinusFactory
import SampLib.Bernoulli.ExpTimesComplement
import SampLib.Bernoulli.ReciprocalExpAffine
import SampLib.Common.WeightedAmplification
import SampLib.Templates
import Metrology.Iris.LocalBI

open ProbLang
open scoped ENNReal NNReal

namespace ExpansionFactoriesReview

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

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


example (E : CoPset) [ProbLangDist.IsUniformInt rT] (a b x y : ℕ)
    (hb : 0 < b) (hba : b ≤ a) (hy : 0 < y) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ReciprocalExpAffine.reciprocalExpAffine_distSpec (rT := rT) (GF := GF)
    E a b x y hb hba hy) F I

section realFactories

variable [ErisGS ℝ hlc GF] [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]

example (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusFactory.expMinusFactory_distSpec E p coin hc) F I

example (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpTimesComplement.expTimesComplement_distSpec E p coin hc) F I

end realFactories

example (p : unitInterval) : (ExpMinusFactory.bias p : ℝ) = Real.exp (-(p : ℝ)) := by
  simp [ExpMinusFactory.bias]
example (p : unitInterval) :
    (ExpTimesComplement.bias p : ℝ) = (1-(p : ℝ))*Real.exp (p : ℝ) := by
  simp [ExpTimesComplement.bias]
example : ExpMinusFactory.bias 0 = 1 := by
  apply Subtype.ext
  simp [ExpMinusFactory.bias]
example : ExpTimesComplement.bias 0 = 1 := by
  apply Subtype.ext
  simp [ExpTimesComplement.bias]
example : ExpTimesComplement.bias 1 = 0 := by
  apply Subtype.ext
  simp [ExpTimesComplement.bias]
example : RealCoin.credit (ExpMinusFactory.bias 0) (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ExpMinusFactory.bias]
example : RealCoin.credit (ExpTimesComplement.bias 0) (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ExpTimesComplement.bias]
example : RealCoin.credit (ExpTimesComplement.bias 1) (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ExpTimesComplement.bias]

example (p : unitInterval) (x : ℝ) :
    ExpMinusFactory.credit p x false (fun _ => ∞) = ∞ := by
  simp only [ExpMinusFactory.credit, ite_self]
  rw [← RealCoin.lintegral_law, MeasureTheory.lintegral_const,
    MeasureTheory.measure_univ, mul_one]

example : (ReciprocalExpAffine.bias 1 1 0 1 (by decide) (by decide) (by decide) : ℝ) = 1/2 := by
  rw [ReciprocalExpAffine.coe_bias]
  norm_num
example : (ReciprocalExpAffine.bias 2 1 0 1 (by decide) (by decide) (by decide) : ℝ) = 1/3 := by
  rw [ReciprocalExpAffine.coe_bias]
  norm_num

-- A persistent step derives the weighted induction without consuming caller resources.
example {α : Type} (t : α → ℝ≥0) (ht : ∀ x, 1 ≤ t x) (P : α → IProp GF)
    (ε : ℝ≥0∞) (hε : 0 < ε) (k : ℝ≥0) (hk : 1 < k) (I : IProp GF) :
    □ (∀ ε : ℝ≥0∞, ⌜0 < ε⌝ -∗
      □ (∀ x, ↯ ((k : ℝ≥0∞) * ε * t x) -∗ P x) -∗
        ∀ x, ↯ (ε * t x) -∗ P x) ∗ I ⊢
      (∀ x, ↯ (ε * t x) -∗ P x) ∗ I := by
  iintro ⟨#Hstep, HI⟩
  isplitl []
  · iapply (ErrorCredit.Induction.weighted t ht P ε hε k hk) $$ Hstep
  · iexact HI

example {α : Type} (t : α → ℝ≥0) (ht : ∀ x, 1 ≤ t x) (P : α → IProp GF)
    (k : ℝ≥0) (hk : 1 < k) :
    □ (∀ ε : ℝ≥0∞, ⌜0 < ε⌝ -∗
      □ (∀ x, ↯ ((k : ℝ≥0∞) * ε * t x) -∗ P x) -∗
        ∀ x, ↯ (ε * t x) -∗ P x) ⊢
      ∀ x, ↯ (∞ * t x) -∗ P x :=
  ErrorCredit.Induction.weighted t ht P ∞ (by simp) k hk

#print axioms SampLib.ExpMinusFactory.expMinusFactory_distSpec
#print axioms SampLib.ExpMinusFactory.expectation
#print axioms SampLib.ExpTimesComplement.expTimesComplement_distSpec
#print axioms SampLib.ExpTimesComplement.expectation
#print axioms SampLib.ExponentialFactory.flip_mass
#print axioms SampLib.ExponentialFactory.growth_step_mass
#print axioms SampLib.ExponentialFactory.amplified_continuation
#print axioms SampLib.ReciprocalExpAffine.reciprocalExpAffine_distSpec
#print axioms SampLib.ReciprocalExpAffine.coe_bias
#print axioms ErrorCredit.Induction.weighted

end
end ExpansionFactoriesReview
