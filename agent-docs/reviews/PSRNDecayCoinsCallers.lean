import SampLib.PSRNDecayCoins
import SampLib.Distributions.LatentReal.IntervalSchedules
import SampLib.Distributions.LatentReal.UniformProduct
import SampLib.Distributions.LatentReal.IntervalRoots
import SampLib.Distributions.PSRNGammaMixtures
import SampLib.Distributions.PSRNBetaRejection
import SampLib.Distributions.PSRNSphereLaw

open SampLib ProbLang
open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (divisor : ℕ) (hd : 0 < divisor) (I : IProp GF) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (p * PSRNDecayCoins.thinning divisor hd)) ∗ I -∗
      tglWp E pl(&(PSRNDecayCoins.callback coin divisor).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((PSRNDecayCoins.distSpec E p coin hcoin divisor hd).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

#print axioms SampLib.PSRNDecayCoins.distSpec
#print axioms SampLib.LatentReal.RationalInterval.contains_multiply
#print axioms SampLib.LatentReal.RationalInterval.contains_reciprocal
#print axioms SampLib.LatentReal.RationalInterval.Approximates.unique
#print axioms SampLib.LatentReal.RationalInterval.Approximates.reciprocal_refine
#print axioms SampLib.PSRNGammaMixtures.lindley_law_eq_withDensity
#print axioms SampLib.PSRNBetaRejection.acceptance_expectation

#print axioms SampLib.LatentUniformProduct.expectation_left
#print axioms SampLib.LatentUniformProduct.law_refines
#print axioms SampLib.LatentReal.exists_doubling_bracket

#print axioms SampLib.PSRNSphereLaw.rotation_invariant
#print axioms SampLib.PSRNSphereLaw.ae_norm_eq_one
