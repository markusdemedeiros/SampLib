import SampLib.Samplers.AlternatingPermutation

open ProbLang
open scoped ENNReal

namespace ExactPermutationCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (odd : Bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (AlternatingPermutationMixture.bias p odd)) ∗ I -∗
      tglWp E
        pl(&Occil.FactoryExtra.alternatingPermutation &coin.fst #int (odd.toNat : ℤ) #())
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  have hs := AlternatingPermutation.alternatingPermutation_distSpec E p hp coin hcoin odd
  iintro ⟨Hcredit, HI⟩
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial

example : (AlternatingPermutationMixture.bias 0 false : ℝ) = 1 := by
  rw [AlternatingPermutationMixture.bias_coe 0 (by norm_num)]
  norm_num

example : (AlternatingPermutationMixture.bias 0 true : ℝ) = 0 := by
  rw [AlternatingPermutationMixture.bias_coe 0 (by norm_num)]
  norm_num

#print axioms SampLib.AlternatingPermutation.alternatingPermutation_distSpec
#print axioms SampLib.AlternatingPermutation.complementOverCosine_distSpec
#print axioms SampLib.AlternatingPermutation.complementTimesTangent_distSpec
#print axioms SampLib.AlternatingPermutationPath.twp_loop
#print axioms SampLib.AlternatingPermutationKernel.expectation
#print axioms SampLib.AlternatingPermutationMixture.bias_coe
#print axioms SampLib.AlternatingPermutationLaw.hasSum_eventMass

end

end ExactPermutationCallers
