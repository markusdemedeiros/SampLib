import SampLib.LatentRealConstructors
import SampLib.LatentMixture
import SampLib.LatentProduct
import SampLib.LatentCompositeMeasuredError
import SampLib.LatentCoinConstants
import SampLib.LatentCoinReciprocal
import SampLib.LatentRational
import SampLib.LatentUnaryViews
import SampLib.LatentLikelihoodRejection
import SampLib.PSRNFloor
import SampLib.LatentFloorAtomless
import SampLib.LatentRationalSubtract
import SampLib.LatentSign
import SampLib.LatentRootViews
import SampLib.LatentRootLaw
import SampLib.LatentUniform
import SampLib.Distributions.AcceptedProposalMap
import SampLib.Distributions.PSRNHyperbolicSecant
import SampLib.Distributions.PSRNRayleigh
import SampLib.Distributions.PSRNFGM
import SampLib.Distributions.PSRNDistributionMixtures

#print axioms SampLib.LatentReal.Root.representedDistSpec
#print axioms SampLib.LatentReal.Root.representedOracleSpec
#print axioms SampLib.LatentReal.Root.represented_viewSpec
#print axioms SampLib.LatentReal.Root.twp_observe
#print axioms SampLib.LatentReal.Root.twp_below
#print axioms SampLib.LatentReal.Root.twp_bracket
#print axioms SampLib.LatentReal.Root.twp_bisect
#print axioms SampLib.LatentReal.Root.expectation_preservation
#print axioms SampLib.LatentReal.Model.rayleigh_law
#print axioms SampLib.LatentReal.Model.rayleigh_admissible
#print axioms SampLib.LatentReal.Sign.latentDistSpec
#print axioms SampLib.LatentReal.Sign.expectation_preservation
#print axioms SampLib.LatentReal.twp_subtractRational
#print axioms SampLib.LatentReal.subtractRational_viewSpec
#print axioms SampLib.LatentReal.Floor.twp_floorScaled
#print axioms SampLib.LatentReal.Floor.expectation_preservation
#print axioms SampLib.LatentReal.Floor.avoidsGrid_of_atomless
#print axioms SampLib.AcceptedProposal.law_map
#print axioms SampLib.PSRNHyperbolicSecant.acceptance_mass
#print axioms SampLib.PSRNHyperbolicSecant.positiveLaw_eq_withDensity
#print axioms SampLib.PSRNHyperbolicSecant.law_eq_withDensity
#print axioms SampLib.PSRNHyperbolicSecant.expectation_preservation
#print axioms SampLib.PSRNRayleigh.expectation_preservation
#print axioms SampLib.PSRNRayleigh.cdf_eq
#print axioms SampLib.PSRNFGM.isProbabilityMeasure_law
#print axioms SampLib.PSRNFGM.expectation_preservation
#print axioms SampLib.PSRNDistributionMixtures.density_one_two
#print axioms SampLib.PSRNDistributionMixtures.density_one_three
#print axioms SampLib.PSRNDistributionMixtures.density_two_three

open MeasureTheory
open scoped ENNReal

example : ProbabilityTheory.cdf SampLib.PSRNRayleigh.law 0 = 0 := by
  simp [SampLib.PSRNRayleigh.cdf_eq]

example (θ : ℝ) (hθ : θ ∈ Set.Icc (-1) 1) :
    (∫⁻ _z, (∞ : ℝ≥0∞) ∂SampLib.PSRNFGM.law θ) = ∞ := by
  have := SampLib.PSRNFGM.isProbabilityMeasure_law hθ
  simp

#print axioms SampLib.LatentReal.PositiveLikelihood.model
#print axioms SampLib.LatentReal.PositiveLikelihood.oracleSpec
#print axioms SampLib.LatentReal.LikelihoodRejection.expectation_preservation
#print axioms SampLib.LatentReal.LikelihoodRejection.newRejection_payloadSpec
#print axioms SampLib.LatentReal.LikelihoodRejection.newRejection_latentDistSpec
#print axioms SampLib.LatentReal.negate_viewSpec
#print axioms SampLib.LatentReal.scaleRational_viewSpec
#print axioms SampLib.LatentReal.negate_oracleSpec
#print axioms SampLib.LatentReal.scaleRational_oracleSpec
#print axioms SampLib.LatentReal.negate_latentDistSpec
#print axioms SampLib.LatentReal.scaleRational_latentDistSpec
#print axioms SampLib.LatentReal.Mixture.latentDistSpec
#print axioms SampLib.LatentReal.Product.payloadSpec
#print axioms SampLib.LatentReal.Product.left_viewSpec
#print axioms SampLib.LatentReal.Product.right_viewSpec
#print axioms SampLib.LatentReal.LatentCoin.constantSpec
#print axioms SampLib.LatentReal.CoinReciprocal.reciprocal_coinSpec

section constructors

open ProbLang SampLib.LatentReal
open Iris Iris.BI Iris.ProofMode ProbLang.TotalEris ProbLang.TotalEris.ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]

example (E : CoPset) :
    IsLatentDistSpec (rT := rT) (GF := GF) E
      pl(let source := &Occil.PSRN.rational #(-3) #5;
        &Occil.PSRN.scaleRational source #(-2) #7)
      ((SampLib.LatentRational.model (-3) 5).scale (((-2 : ℤ) : ℝ) / (7 : ℤ))) ()
      (scaleRationalOwns (SampLib.LatentRational.owns (-3) 5) (-2) 7) :=
  scaleRational_latentDistSpec E _ _ () _
    (SampLib.LatentRational.rational_latentDistSpec E (-3) 5 (by decide)) (-2) 7 (by decide)

example (E : CoPset) :
    IsLatentPayloadSpec (rT := rT) (GF := GF) E
      (Product.code pl(&Occil.PSRN.rational #(-3) #5) pl(&Occil.PSRN.rational #2 #7))
      (ProductModel.left (SampLib.LatentRational.model (-3) 5)
        (SampLib.LatentRational.model 2 7)) ((), ())
      (Product.pairOwns (SampLib.LatentRational.owns (-3) 5)
        (SampLib.LatentRational.owns 2 7)) :=
  Product.payloadSpec E _ _ (by is_lc) _ _ () () _ _
    (SampLib.LatentRational.rational_latentDistSpec E (-3) 5 (by decide))
    (SampLib.LatentRational.rational_latentDistSpec E 2 7 (by decide))

example : Floor.AvoidsGrid (SampLib.LatentRational.model 2 3) 2 () := by
  apply MeasureTheory.ae_of_all
  intro x
  norm_num [Floor.output, SampLib.LatentRational.model]

example (E : CoPset) [ProbLangDist.IsUniformInt rT] :
    IsRepresentedDistSpec (rT := rT) (GF := GF) E
      pl(let source := &Occil.PSRN.newUniform #(); &Occil.PSRN.root source #2)
      (SampLib.LatentUniform.model.nthRoot 2)
      (SampLib.LatentUniform.model.nthRoot 2).dyadicRepresentation []
      (Root.owns SampLib.LatentUniform.model 2 SampLib.LatentUniform.owns) := by
  let _ : MeasureTheory.NullSingletonClass (SampLib.LatentUniform.model.law []) := by
    rw [SampLib.LatentUniform.model_initial_law]
    change MeasureTheory.NullSingletonClass
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1))
    infer_instance
  have hD : SampLib.LatentUniform.model.MeasurableError := fun _ => measurable_const
  have hdom : Root.Admissible SampLib.LatentUniform.model 2 [] :=
    Root.Admissible.of_atomless _ _ _
      ((SampLib.DyadicPosterior.ae_mem_unit []).mono fun _ hx => hx.1)
  exact Root.representedDistSpec E _ _ hD [] _
    (SampLib.LatentUniform.newUniform_latentDistSpec E) 2 (by decide) hdom

end constructors
