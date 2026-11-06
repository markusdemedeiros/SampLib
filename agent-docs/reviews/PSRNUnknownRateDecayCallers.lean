import SampLib.PSRNUnknownRateDecay

open ProbLang SampLib
open scoped ENNReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (d : ℕ) (hd : 0 < d) (F : Bool → ℝ≥0∞) (R : IProp GF) :
    ⊢ R ∗ ↯ (∫⁻ b, F b ∂RealCoin.law
      (ExpMinusFactory.bias (p * PSRNDecayCoins.thinning d hd))) -∗
      tglWp E pl(&(PSRNUnknownRateDecay.value coin).fst #int (d : ℤ))
        (fun result : Val ℝ => iprop(∃ b : Bool,
          ⌜result = Val.bool b⌝ ∗ R ∗ ↯ (F b))) := by
  iintro ⟨HR, Hcredit⟩
  iapply (PSRNUnknownRateDecay.distSpec E p coin hcoin d hd).wp
    F (measurable_of_countable _) _ $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe HR Hcredit
  itrivial

example (d : ℕ) (hd : 0 < d) :
    (ExpMinusFactory.bias ((0 : unitInterval) * PSRNDecayCoins.thinning d hd) : ℝ) = 1 := by
  rw [PSRNUnknownRateDecay.bias_value]
  simp

#print axioms SampLib.PSRNUnknownRateDecay.distSpec
#print axioms SampLib.PSRNUnknownRateDecay.bias_value
