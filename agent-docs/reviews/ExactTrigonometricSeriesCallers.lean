import SampLib.Bernoulli.TrigonometricSeriesFactories
import SampLib.Bernoulli.ArcsineFactories

open ProbLang
open scoped ENNReal

namespace ExactTrigonometricSeriesCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law
      (AlternatingSeries.meanBias TrigonometricFactoryParameters.cosine p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.cosineSqrt &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := TrigonometricSeriesFactories.cosineSqrt_distSpec E p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 6 * b)
    (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (AlternatingSeries.meanBias
      (TrigonometricSeriesFactories.sincParameters a b hb hab) p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.sincSqrtScaled &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := TrigonometricSeriesFactories.sincSqrtScaled_distSpec E a b ha hb hab p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 6 * b)
    (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (AlternatingSeries.meanBias
      (TrigonometricSeriesFactories.sincParameters a b hb hab) (p * p))) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.sincScaled &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := TrigonometricSeriesFactories.sincScaled_distSpec E a b ha hb hab p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (ArcsineFactoryParameters.bias p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.arcsinePlusSqrtMinusOne &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := ArcsineFactories.arcsinePlusSqrtMinusOne_distSpec E p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (ArcsineFactories.halfBias p)) ∗ I -∗
      tglWp E pl(&Occil.FactoryExtra.arcsineHalf &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := ArcsineFactories.arcsineHalf_distSpec E p coin hcoin
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example : (ArcsineFactoryParameters.bias 0 : ℝ) = 0 := by
  rw [ArcsineFactoryParameters.bias_coe]
  norm_num

example : (ArcsineFactoryParameters.bias 1 : ℝ) = Real.pi / 2 - 1 := by
  rw [ArcsineFactoryParameters.bias_coe]
  norm_num

example : (ArcsineFactories.halfBias 0 : ℝ) = 0 := by
  rw [ArcsineFactories.halfBias_coe]
  norm_num

example : (ArcsineFactories.halfBias 1 : ℝ) = Real.pi / 4 := by
  rw [ArcsineFactories.halfBias_coe]
  norm_num
  ring

#print axioms SampLib.TrigonometricSeriesFactories.cosineSqrt_distSpec
#print axioms SampLib.TrigonometricSeriesFactories.sincSqrtScaled_distSpec
#print axioms SampLib.TrigonometricSeriesFactories.sincScaled_distSpec
#print axioms SampLib.ArcsineFactories.arcsinePlusSqrtMinusOne_distSpec
#print axioms SampLib.ArcsineFactories.arcsineHalf_distSpec

#print axioms SampLib.ArcsineFactoryParameters.bias_coe
#print axioms SampLib.ArcsineFactories.halfBias_coe

end

end ExactTrigonometricSeriesCallers
