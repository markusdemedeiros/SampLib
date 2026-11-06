import SampLib.Bernoulli.POverTangent
import SampLib.Bernoulli.ArctanFactory

open ProbLang
open scoped ENNReal

namespace ExactTrigonometricCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (e f : ℤ) (he : 0 < e) (hef : e < f)
    (hgap : (e : ℝ) / f ≤ Real.sin p - p * Real.cos p)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (POverTangent.bias p e f he hef hgap)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.pOverTangent &coin.fst #int e #int f #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := POverTangent.pOverTangent_distSpec E p coin hcoin e f he hef hgap
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (ArctanOverPFactory.bias p)) ∗ I -∗
      tglWp E pl(&Occil.arctanOverPFactory &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := ArctanOverPFactory.arctanOverPFactory_distSpec E p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (ArctanFactory.bias p)) ∗ I -∗
      tglWp E pl(&Occil.arctanFactory &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := ArctanFactory.arctanFactory_distSpec E p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example : (ArctanOverPFactory.bias 0 : ℝ) = 1 := ArctanFactory.ratio_coe_zero
example : (ArctanFactory.bias 0 : ℝ) = 0 := by simp
example : (ArctanFactory.bias 1 : ℝ) = Real.pi / 4 := by simp

#print axioms SampLib.ArctanOverPFactory.arctanOverPFactory_distSpec
#print axioms SampLib.ArctanFactory.arctanFactory_distSpec
#print axioms SampLib.ArctanFactory.success_mass
#print axioms SampLib.ArctanOverPFactory.expectation

#print axioms SampLib.POverTangent.pOverTangent_distSpec
#print axioms SampLib.POverTangent.bias_coe
#print axioms SampLib.POverTangent.gap

end

end ExactTrigonometricCallers
