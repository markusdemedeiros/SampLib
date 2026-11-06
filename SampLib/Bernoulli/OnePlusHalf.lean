import SampLib.Uniform.FairCoin
import Samplers.Bernoulli.Elementary
import Metrology.Iris.LocalBI

/-! # The Bernoulli factory `(1+p)/2` -/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal

namespace SampLib.OnePlusHalf

noncomputable section

/-- Output bias, including both endpoints of the input domain. -/
def bias (p : unitInterval) : unitInterval :=
  ⟨(1 + (p : ℝ)) / 2, by constructor <;> linarith [p.2.1, p.2.2]⟩

/-- Continuation credit after the fair selector. -/
def kernel (p : unitInterval) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else ∫⁻ x, F x ∂RealCoin.law p

/-- A fair choice between `true` and a p-coin gives bias `(1+p)/2`. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, kernel p F b ∂RealCoin.law VonNeumann.fairBias =
      ∫⁻ b, F b ∂RealCoin.law (bias p) := by
  have ht : ofReal (bias p : ℝ) = ofReal (1 / 2 : ℝ) +
      ofReal (1 / 2 : ℝ) * ofReal (p : ℝ) := by
    rw [← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (by norm_num) (mul_nonneg (by norm_num) p.2.1)]
    congr 1
    dsimp [bias]
    ring
  have hf : ofReal (1 - (bias p : ℝ)) =
      ofReal (1 / 2 : ℝ) * ofReal (1 - (p : ℝ)) := by
    rw [← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    dsimp [bias]
    ring
  rw [RealCoin.lintegral_law, RealCoin.lintegral_law]
  norm_num [kernel, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
    VonNeumann.fairBias, ht, hf]
  ring

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Typed specification from an abstract p-coin. -/
theorem onePlusHalf_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.onePlusHalf &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_pure
    twp_bind pl(&Occil.fairCoin #())
    isimp only [← expectation p F] at Hcredit
    iapply ((FairCoin.fairCoin_distSpec E).wp (kernel p F) (measurable_of_countable _) _)
      $$ Hcredit
    iintro %b Hcredit
    cases b
    · isimp only [kernel, Bool.false_eq_true, ite_false] at Hcredit
      twp_pures
      iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit
    · isimp only [kernel, ite_true] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists true
      iframe Hcredit
      ipureintro
      rfl

end specification

end

end SampLib.OnePlusHalf
