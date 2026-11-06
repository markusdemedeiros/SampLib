import SampLib.PSRN.Support.PSRNExponentialDecay
import SampLib.PSRN.Support.PSRNRationalRateDecay
import SampLib.PSRN.Support.PSRNLogRateDecay
import SampLib.PSRN.Support.PSRNUnknownRateDecay

/-! # Concrete callbacks for the decay-based exponential sampler -/

open ProbLang Iris TotalEris

namespace SampLib.PSRNExponential

noncomputable section

section integer

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

/-- Exact integer trials give every positive rational rate. -/
theorem rational_isDecaySpec (E : CoPset) (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    IsDecaySpec (GF := GF) E ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb)
      (PSRNRationalRateDecay.value a b) where
  spec d hd := by
    have heq : ExpMinusRational.bias a (b * d) ha.le (mul_pos hb (by exact_mod_cast hd)) =
        decayBias ((a : ℝ) / b) (PSRNRationalRateDecay.rate_pos a b ha hb) d hd := by
      apply Subtype.ext
      rw [PSRNRationalRateDecay.bias_value a b ha.le hb d hd]
      simp only [decayBias, neg_div]
    simpa only [heq] using PSRNRationalRateDecay.distSpec E a b ha.le hb d hd

/-- The rational-power factory supplies a logarithmic rate without evaluating a logarithm. -/
theorem logRate_isDecaySpec (E : CoPset) (x y : ℤ) (hy : 0 < y) (hxy : y < x) :
    IsDecaySpec (GF := GF) E (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy)
      (PSRNLogRateDecay.value x y) where
  spec d hd := by
    have heq : RationalPower.bias (PSRNLogRateDecay.base x y hy hxy) 1 d hd =
        decayBias (PSRNLogRateDecay.rate x y) (PSRNLogRateDecay.rate_pos hy hxy) d hd := by
      apply Subtype.ext
      rw [PSRNLogRateDecay.bias_value x y hy hxy d hd]
      simp only [decayBias, neg_div]
    simpa only [heq] using PSRNLogRateDecay.distSpec E x y hy hxy d hd

end integer

section unknown

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]

/-- Repeated calls use the supplied coin specification, with no probability parameter in code. -/
theorem unknownRate_isDecaySpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDecaySpec (GF := GF) E (p : ℝ) hp (PSRNUnknownRateDecay.value coin) where
  spec d hd := by
    have heq : ExpMinusFactory.bias (p * PSRNDecayCoins.thinning d hd) =
        decayBias (p : ℝ) hp d hd := by
      apply Subtype.ext
      rw [PSRNUnknownRateDecay.bias_value p d hd]
      simp only [decayBias, neg_div]
    simpa only [heq] using PSRNUnknownRateDecay.distSpec E p coin hcoin d hd

end unknown

end

end SampLib.PSRNExponential
