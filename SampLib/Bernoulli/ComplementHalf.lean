import SampLib.Bernoulli.OnePlusHalf
import SampLib.Bernoulli.Complement
import Samplers.Bernoulli.Elementary
import Metrology.Iris.LocalBI

/-! # The Bernoulli factory `(1-p)/2` -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ComplementHalf

noncomputable section

/-- Output bias. -/
def bias (p : unitInterval) : unitInterval := unitInterval.symm (OnePlusHalf.bias p)

theorem bias_coe (p : unitInterval) : (bias p : ℝ) = (1 - (p : ℝ)) / 2 := by
  simp only [bias, unitInterval.coe_symm_eq, OnePlusHalf.bias]
  ring

/-- Continuation credit after the fair selector. -/
def kernel (p : unitInterval) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else ∫⁻ x, F (!x) ∂RealCoin.law p

/-- Complementing the `(1+p)/2` mixture gives bias `(1-p)/2`. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, kernel p F b ∂RealCoin.law VonNeumann.fairBias =
      ∫⁻ b, F b ∂RealCoin.law (bias p) := by
  change _ = ∫⁻ b, F b ∂Complement.law (OnePlusHalf.bias p)
  rw [← Complement.expectation_preservation]
  simpa only [kernel, OnePlusHalf.kernel, Bool.not_true] using
    OnePlusHalf.expectation p (fun b => F (!b))

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Typed specification from an abstract p-coin. -/
theorem complementHalf_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementHalf &coin.fst #())
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
      twp_bind pl(&coin.fst #())
      iapply (hcoin.wp (fun x => F (!x)) (measurable_of_countable _) _) $$ Hcredit
      iintro %x Hcredit
      twp_pures
      twp_value
      imodintro
      iexists !x
      iframe Hcredit
      ipureintro
      simp only [Val.ext_iff, bool_not]
    · isimp only [kernel, ite_true] at Hcredit
      twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      ipureintro
      rfl

end specification

end

end SampLib.ComplementHalf
