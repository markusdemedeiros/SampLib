import SampLib.Samplers.RationalChoice
import SampLib.Distributions.DiscreteLaplace
import SampLib.Distributions.FisherMultivariate
import SampLib.NatUrnOps
import SampLib.Samplers.UniformBinaryFloat
import Metrology.Iris.LocalBI

open Set ProbLang
open scoped ENNReal NNReal

namespace ExpansionDiscreteAudit

noncomputable section

section mathematics

open MeasureTheory Measure SampLib

example : RationalChoice.denominator [(1, 2), (1, 3)] = 6 := by decide
example : RationalChoice.normalize 6 [(1, 2), (1, 3)] = [3, 2] := by decide
example : RationalChoice.normalize 12 [(2, 4), (1, 3)] = [6, 4] := by decide

example : RationalChoice.law [(1, 2), (1, 3)] (by simp) (by decide) {0} =
    (3 : ℝ≥0∞) / 5 := by
  rw [RationalChoice.law_singleton]
  norm_num [RationalChoice.total, RationalChoice.weightedSum]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by finiteness) (by simp)) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]

example : RationalChoice.law [(1, 2), (1, 3)] (by simp) (by decide) {1} =
    (2 : ℝ≥0∞) / 5 := by
  rw [RationalChoice.law_singleton]
  norm_num [RationalChoice.total, RationalChoice.weightedSum]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.div_ne_top (by finiteness) (by simp)) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]

example : RationalChoice.law [(0, 3), (2, 5), (0, 7)] (by simp) (by decide) {0} = 0 := by
  rw [RationalChoice.law_singleton]
  norm_num

example (F : ℕ → ℝ≥0∞) :
    (∫⁻ i, F i ∂RationalChoice.law [(7, 13)] (by simp) (by decide)) = F 0 := by
  rw [RationalChoice.law, WeightedChoice.lintegral_law]
  norm_num [RationalChoice.normalize, RationalChoice.denominator, WeightedChoice.weightedSum]
  rw [mul_comm (7 : ℝ≥0∞), ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]

example : (∫⁻ i, (if i = 1 then 2 else ∞ : ℝ≥0∞)
    ∂RationalChoice.law [(0, 3), (2, 5), (0, 7)] (by simp) (by decide)) = 2 := by
  rw [RationalChoice.law, WeightedChoice.lintegral_law]
  norm_num [RationalChoice.normalize, RationalChoice.denominator, WeightedChoice.weightedSum]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

example (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < RationalChoice.numerators ws) :
    (∫⁻ _i, (∞ : ℝ≥0∞) ∂RationalChoice.law ws hden hs) = ∞ := by simp

example : DiscreteLaplace.acceptance 3 2 (by decide) (0, (1, false)) = 0 := by
  norm_num [DiscreteLaplace.acceptance, DiscreteLaplace.magnitude]

example : DiscreteLaplace.acceptance 3 2 (by decide) (0, (1, true)) = 1 := by
  apply Subtype.ext
  norm_num [DiscreteLaplace.acceptance, DiscreteLaplace.magnitude, ExpMinusRational.bias]

example : DiscreteLaplace.output 3 2 (0, (1, false)) = 0 := by
  decide

example : DiscreteLaplace.output 3 2 (1, (1, false)) = -1 := by
  decide

example : DiscreteLaplace.law 2 3 (by decide) (by decide) {1} =
    DiscreteLaplace.law 2 3 (by decide) (by decide) {-1} := by
  simp only [DiscreteLaplace.law_singleton]
  norm_num

example : DiscreteLaplace.law 3 2 (by decide) (by decide) {1} =
    DiscreteLaplace.coefficient 3 2 * ENNReal.ofReal (Real.exp (-(3 : ℝ) / 2)) := by
  rw [DiscreteLaplace.law_singleton]
  norm_num [DiscreteLaplace.expWeight]

example : DiscreteLaplace.law 3 2 (by decide) (by decide) {0} =
    DiscreteLaplace.coefficient 3 2 := by
  rw [DiscreteLaplace.law_singleton]
  norm_num

example (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    (∫⁻ _z, (∞ : ℝ≥0∞) ∂DiscreteLaplace.law s t hs ht) = ∞ := by simp

example (F : ℤ → ℝ≥0∞) :
    ∫⁻ z, AcceptedProposal.weight (DiscreteLaplace.acceptance 3 2 (by decide)) z *
      F (DiscreteLaplace.output 3 2 z) ∂DiscreteLaplace.proposal 2 (by decide) =
        DiscreteLaplace.normalizer 3 2 *
          (∫⁻ k, F k ∂DiscreteLaplace.law 3 2 (by decide) (by decide)) :=
  DiscreteLaplace.weighted_expectation 3 2 (by decide) (by decide) F

#print axioms SampLib.DiscreteLaplace.weighted_expectation
#print axioms SampLib.DiscreteLaplace.accepted_map_eq
#print axioms SampLib.DiscreteLaplace.law_singleton

example : FisherMultivariate.allocation 3 [0, 2, 4] = [0, 2, 1] := by decide
example : FisherMultivariate.coefficient [2, 1] [1, 3] [1, 0] = 2 := by decide
example : FisherMultivariate.coefficient [2, 1] [1, 3] [0, 1] = 3 := by decide

example : FisherMultivariate.law 1 [2, 1] [1, 3] rfl (by simp) (by decide) {[0, 1]} * 2 =
    3 * FisherMultivariate.law 1 [2, 1] [1, 3] rfl (by simp) (by decide) {[1, 0]} := by
  have hn : 0 < FisherMultivariate.normalizer 1 [2, 1] [1, 3] :=
    FisherMultivariate.normalizer_pos 1 [2, 1] [1, 3] rfl (by simp) (by decide)
  rw [FisherMultivariate.law_singleton, FisherMultivariate.law_singleton]
  norm_num [FisherMultivariate.coefficient]
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_ofNat 3,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

example : FisherMultivariate.law 0 [] [] rfl (by simp) (by decide) = Measure.dirac [] := by
  simpa using FisherMultivariate.law_zero [] [] rfl (by simp)

example : FisherMultivariate.law 3 [0, 2, 1] [5, 1, 3] rfl (by simp) (by decide) =
    Measure.dirac [0, 2, 1] := by
  simpa using FisherMultivariate.law_full [0, 2, 1] [5, 1, 3] rfl (by simp)

example : FisherMultivariate.law 1 [0, 2] [5, 3] rfl (by simp) (by decide) {[1, 0]} = 0 := by
  rw [FisherMultivariate.law_singleton]
  norm_num [FisherMultivariate.coefficient]

example : FisherMultivariate.law 1 [2, 1] [1, 3] rfl (by simp) (by decide) {[1]} = 0 := by
  rw [FisherMultivariate.law_singleton]
  norm_num [FisherMultivariate.coefficient]

example (counts odds : List ℕ) (hlen : counts.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) :
    (∫⁻ xs, (if xs = counts then 3 else ∞ : ℝ≥0∞)
      ∂FisherMultivariate.law counts.sum counts odds hlen hodds le_rfl) = 3 := by
  rw [FisherMultivariate.law_full]
  simp

#print axioms SampLib.FisherMultivariate.proposal_singleton
#print axioms SampLib.FisherMultivariate.mass_nonzero
#print axioms SampLib.FisherMultivariate.law_singleton
#print axioms SampLib.FisherMultivariate.law_support

private theorem float_mass_credit (p cap : ℕ) (x : ℤ × ℤ) :
    UniformBinaryFloat.law p cap {x} =
      UniformBinaryFloat.credit p cap 0 (fun y => if y = x then 1 else 0) := by
  rw [← lintegral_indicator_one (measurableSet_singleton x)]
  simp only [UniformBinaryFloat.credit, Set.indicator, Set.mem_singleton_iff, Pi.one_apply]

private theorem float_credit_step (p cap offset : ℕ) (F : ℤ × ℤ → ℝ≥0∞) :
    UniformBinaryFloat.credit p (cap + 1) offset F =
      RealCoin.pmf VonNeumann.fairBias true *
        (∫⁻ m, F (UniformBinaryFloat.point p offset m) ∂UniformInt.law (2 ^ p)) +
      RealCoin.pmf VonNeumann.fairBias false * UniformBinaryFloat.credit p cap (offset + 1) F := by
  rw [← UniformBinaryFloat.expectation p cap offset F, RealCoin.lintegral_law]
  simp [RealCoin.credit, UniformBinaryFloat.coinCredit]

example (p : ℕ) : UniformBinaryFloat.law p 0 = dirac (0, 0) := by simp

example : UniformBinaryFloat.law 2 2 {(0, 0)} = (1 : ℝ≥0∞) / 4 := by
  rw [float_mass_credit, float_credit_step 2 1, float_credit_step 2 0]
  norm_num [UniformInt.lintegral_law, UniformBinaryFloat.point, Finset.sum_range_succ,
    RealCoin.pmf, VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

example : UniformBinaryFloat.law 2 2 {(4, -3)} = (1 : ℝ≥0∞) / 8 := by
  rw [float_mass_credit, float_credit_step 2 1, float_credit_step 2 0]
  norm_num [UniformInt.lintegral_law, UniformBinaryFloat.point, Finset.sum_range_succ,
    RealCoin.pmf, VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

example : UniformBinaryFloat.law 2 2 {(7, -4)} = (1 : ℝ≥0∞) / 16 := by
  rw [float_mass_credit, float_credit_step 2 1, float_credit_step 2 0]
  norm_num [UniformInt.lintegral_law, UniformBinaryFloat.point, Finset.sum_range_succ,
    RealCoin.pmf, VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton]

private theorem float_cutoff_mass : UniformBinaryFloat.law 2 2 {(4, -5)} = 0 := by
  rw [float_mass_credit, float_credit_step 2 1, float_credit_step 2 0]
  norm_num [UniformInt.lintegral_law, UniformBinaryFloat.point, Finset.sum_range_succ,
    RealCoin.pmf, VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]

example : UniformBinaryFloat.law 0 1 {(1, -1)} = (1 : ℝ≥0∞) / 2 := by
  rw [float_mass_credit, float_credit_step 0 0]
  norm_num [UniformInt.lintegral_law, UniformBinaryFloat.point, Finset.sum_range_succ,
    RealCoin.pmf, VonNeumann.fairBias, ENNReal.ofReal_div_of_pos]

example : (∫⁻ x, ({(4, -5)} : Set (ℤ × ℤ)).indicator (fun _ => ∞) x
    ∂UniformBinaryFloat.law 2 2) = 0 := by
  rw [lintegral_indicator_const (measurableSet_singleton _), float_cutoff_mass, mul_zero]

example (p cap : ℕ) : (∫⁻ _x, (∞ : ℝ≥0∞) ∂UniformBinaryFloat.law p cap) = ∞ := by simp

end mathematics

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (ws : List (ℕ × ℕ)) (hden : ∀ p ∈ ws, 0 < p.2)
    (hs : 0 < RationalChoice.numerators ws) (F : ℕ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂RationalChoice.law ws hden hs) ∗ I -∗
      tglWp E pl(&Occil.Weighted.rationalChoice &(listVal RationalChoice.fractionVal ws).fst #())
        (fun v : Val rT => iprop(∃ i : ℕ, ⌜v = Val.int (i : ℤ)⌝ ∗ ↯ (F i) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((RationalChoice.rationalChoice_distSpec E ws hden hs).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit HI
  itrivial

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.rationalChoice
      &(listVal RationalChoice.fractionVal [(2, 4), (1, 3)]).fst #())
    (RationalChoice.law [(2, 4), (1, 3)] (by simp) (by decide))
    (fun i : ℕ => Val.int (i : ℤ)) :=
  RationalChoice.rationalChoice_distSpec E _ (by simp) (by decide)

#print axioms SampLib.RationalChoice.rationalChoice_distSpec
#print axioms SampLib.RationalChoice.scale_expectation
#print axioms SampLib.RationalChoice.lintegral_law
#print axioms SampLib.RationalChoice.law_singleton

omit [ProbLangDist.IsUniformInt rT] in
private theorem pure_frame {E : CoPset} {e : Exp rT} {value : Val rT}
    (h : ⊢ tglWp E e (fun v => iprop(⌜v = value⌝))) (I : IProp GF) :
    ⊢ I -∗ tglWp E e (fun v => iprop(⌜v = value⌝ ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply h
  iintro %v %hv
  iframe HI
  itrivial

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (pop odds : List ℕ) (hlen : pop.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.DiscreteExtra.validUrn
      &(NatCounters.encode pop).fst &(NatCounters.encode odds).fst)
      (fun v => iprop(⌜v = Val.bool true⌝ ∗ I)) :=
  pure_frame (NatUrnOps.twp_validUrn E pop odds hlen hodds) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) (pop odds : List ℕ) (hlen : pop.length ≤ odds.length) (I : IProp GF) :
    ⊢ I -∗ tglWp E pl(&Occil.DiscreteExtra.urnWeights
      &(NatCounters.encode pop).fst &(NatCounters.encode odds).fst)
      (fun v => iprop(⌜v = NatCounters.encode (List.zipWith Nat.mul pop odds)⌝ ∗ I)) :=
  pure_frame (NatUrnOps.twp_urnWeights E pop odds hlen) I

omit [ProbLangDist.IsUniformInt rT] in
example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.urnWeights
      &(NatCounters.encode [0, 2, 1]).fst &(NatCounters.encode [7, 3, 5, 9]).fst)
      (fun v => iprop(⌜v = NatCounters.encode [0, 6, 5]⌝)) := by
  simpa using NatUrnOps.twp_urnWeights (rT := rT) (GF := GF) E [0, 2, 1] [7, 3, 5, 9]
    (by decide)

#print axioms SampLib.NatUrnOps.twp_validUrn
#print axioms SampLib.NatUrnOps.twp_urnWeights

example (E : CoPset) (p cap : ℕ) (F : ℤ × ℤ → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂UniformBinaryFloat.law p cap) ∗ I -∗
      tglWp E pl(&Occil.Weighted.uniformBinaryFloat #int (p : ℤ) #int (cap : ℤ) #())
        (fun v : Val rT => iprop(∃ x : ℤ × ℤ,
          ⌜v = UniformBinaryFloat.encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((UniformBinaryFloat.uniformBinaryFloat_distSpec E p cap).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial

example (E : CoPset) : IsDistSpec (GF := GF) E
    pl(&Occil.Weighted.uniformBinaryFloat #0 #0 #())
    (MeasureTheory.Measure.dirac (0, 0)) UniformBinaryFloat.encode := by
  simpa only [UniformBinaryFloat.law, UniformBinaryFloat.lawFrom_zero, Nat.cast_zero] using
    UniformBinaryFloat.uniformBinaryFloat_distSpec E 0 0

#print axioms SampLib.UniformBinaryFloat.uniformBinaryFloat_distSpec
#print axioms SampLib.UniformBinaryFloat.expectation
#print axioms SampLib.UniformBinaryFloat.lawFrom_zero

end

end ExpansionDiscreteAudit
