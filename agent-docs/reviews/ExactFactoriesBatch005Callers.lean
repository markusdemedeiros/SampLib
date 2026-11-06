import SampLib.Bernoulli.SampleGeometricBag
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Metrology.TotalEris.Examples.Samplers.RealDecrTrial

open ProbLang
open scoped ENNReal

namespace ExactFactoriesReview005

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem frame (E : CoPset) (l : Loc) (p : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p LatentBernoulli.bias G)) ∗ I) ⊢
      tglWp E pl(&Occil.sampleGeometricBag #loc l #())
        (fun v : Val rT => iprop(∃ (b : Bool) (q : List Bool),
          ⌜v = Val.bool b ∧ p <+: q⌝ ∗ UniformBag.owns l q ∗
          ↯ (DyadicPosterior.credit q (G b)) ∗ I)) := by
  iintro ⟨⟨Hbag, Hcredit⟩, HI⟩
  iapply ((SampleGeometricBag.sampleGeometricBag_coinSpec E l).wp p G hG _) $$ Hbag Hcredit
  iintro %b %q %hpq Hbag Hcredit
  iexists b, q
  iframe Hbag Hcredit HI
  ipureintro
  exact ⟨rfl, hpq⟩

/-- Both syntactic aliases consume and return the same owned bag, with joint latent credit. -/
theorem twice (E : CoPset) (l bagAlias : Loc) (halias : bagAlias = l) (p : List Bool)
    (G : Bool → Bool → ℝ → ℝ≥0∞) (hG : ∀ b c, Measurable (G b c)) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p LatentBernoulli.bias
      (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (G b) u))) ∗ I) ⊢
      tglWp E pl(let first := &Occil.sampleGeometricBag #loc l #();
        let second := &Occil.sampleGeometricBag #loc bagAlias #(); (first, second))
        (fun v : Val rT => iprop(∃ (b c : Bool) (q : List Bool),
          ⌜v = Val.pair (Val.bool b) (Val.bool c) ∧ p <+: q⌝ ∗
          UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (G b c)) ∗ I)) := by
  subst bagAlias
  iintro ⟨⟨Hbag, Hcredit⟩, HI⟩
  twp_bind pl(&Occil.sampleGeometricBag #loc l #())
  iapply ((SampleGeometricBag.sampleGeometricBag_coinSpec E l).wp p
    (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (G b) u)
    (fun b => LatentBernoulli.measurable_kernel LatentBernoulli.measurable_bias (hG b)) _)
    $$ Hbag Hcredit
  iintro %b %q %hpq Hbag Hcredit
  twp_pure
  twp_bind pl(&Occil.sampleGeometricBag #loc l #())
  have hfold : DyadicPosterior.credit q
      (fun u => LatentBernoulli.kernel LatentBernoulli.bias (G b) u) =
        LatentBernoulli.credit q LatentBernoulli.bias (G b) := rfl
  isimp only [hfold] at Hcredit
  iapply ((SampleGeometricBag.sampleGeometricBag_coinSpec E l).wp q (G b) (hG b) _)
    $$ Hbag Hcredit
  iintro %c %r %hqr Hbag Hcredit
  twp_pures
  twp_value
  imodintro
  iexists b, c, r
  iframe Hbag Hcredit HI
  ipureintro
  exact ⟨rfl, hpq.trans hqr⟩

example (E : CoPset) (l : Loc) (I : IProp GF) :=
  twice E l l rfl [] (fun b c u => if b && c then ENNReal.ofReal u else ∞)
    (by intro b c; cases b <;> cases c <;> fun_prop) I

private def bothTrue (b c : Bool) (_ : ℝ) : ℝ≥0∞ := if b && c then 1 else 0

private theorem unit_second_moment :
    (∫⁻ u, ENNReal.ofReal (u ^ 2) ∂DyadicPosterior.unitLaw) = (1 : ℝ≥0∞) / 3 := by
  change (∫⁻ u in Set.Ico (0 : ℝ) 1, ENNReal.ofReal (u ^ 2)) = _
  rw [MeasureTheory.restrict_Ico_eq_restrict_Icc,
    ProbLang.TotalEris.Examples.lintegral_ofReal_Icc (by norm_num) (by fun_prop)
      (fun u _ => sq_nonneg u), integral_pow]
  norm_num [ENNReal.ofReal_div_of_pos]

/-- Shared latent probability gives joint success `E[U²]=1/3`, not `1/4`. -/
example :
    LatentBernoulli.credit [] LatentBernoulli.bias
      (fun b u => LatentBernoulli.kernel LatentBernoulli.bias (bothTrue b) u) =
        (1 : ℝ≥0∞) / 3 := by
  unfold LatentBernoulli.credit LatentBernoulli.kernel bothTrue RealCoin.credit RealCoin.pmf
  simp only [Bool.and_true, Bool.and_false, ite_true, Bool.false_eq_true, ite_false,
    mul_one, mul_zero, add_zero]
  unfold DyadicPosterior.credit
  rw [DyadicPosterior.law_nil]
  calc
    _ = ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂DyadicPosterior.unitLaw := by
      apply MeasureTheory.lintegral_congr_ae
      have hu : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Set.Ico 0 1 := by
        simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
      filter_upwards [hu] with u hu
      rw [LatentBernoulli.bias_coe hu]
      simp only [pow_two, ENNReal.ofReal_mul hu.1]
    _ = _ := unit_second_moment

#print axioms SampleGeometricBag.sampleGeometricBag_coinSpec
#print axioms SampleGeometricBag.twp_sampleGeometricBag
#print axioms UniformBag.IsCoinSpec.wp

end

end ExactFactoriesReview005
