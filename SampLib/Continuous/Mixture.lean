import SampLib.Uniform.RealCoin
import Samplers.Continuous
import Metrology.Iris.LocalBI

/-! # Mixtures selected by an abstract Bernoulli coin -/

open ProbLang
open scoped ENNReal

namespace SampLib.Mixture

noncomputable section

section mathematics

open MeasureTheory Measure

variable {α : Type _} [MeasurableSpace α]

/-- Select `μ` with probability `p` and `ν` otherwise. -/
def law (p : unitInterval) (μ ν : Measure α) : Measure α :=
  (RealCoin.pmf p true • μ) + (RealCoin.pmf p false • ν)

instance (p : unitInterval) (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (law p μ ν) where
  measure_univ := by simpa [law] using RealCoin.pmf_sum p

/-- Mixture expectation is the coin expectation of component expectations. -/
theorem expectation_preservation (p : unitInterval) (μ ν : Measure α)
    (F : α → ℝ≥0∞) :
    ∫⁻ x, F x ∂law p μ ν =
      RealCoin.credit p (fun b => if b then ∫⁻ x, F x ∂μ else ∫⁻ x, F x ∂ν) := by
  simp [law, RealCoin.credit, smul_eq_mul]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] {μ ν : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
local bi (IProp GF)

/-- CTE composition of a selector and its two component samplers. -/
theorem twp_mixture (E : CoPset) (p : unitInterval) (coin left right : Val rT)
    (encode : α → Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) μ encode)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) ν encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ x, F x ∂law p μ ν) -∗
      tglWp E pl(&Occil.mixture &coin.fst &left.fst &right.fst #())
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [expectation_preservation, ← RealCoin.lintegral_law] at Hcredit
  iapply (hcoin.wp _ (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pures
    isimp only [Bool.false_eq_true, ite_false] at Hcredit
    iapply hright.spec F hF $$ Hcredit
  · twp_pures
    isimp only [ite_true] at Hcredit
    iapply hleft.spec F hF $$ Hcredit

/-- Typed mixture specification. -/
theorem mixture_distSpec (E : CoPset) (p : unitInterval) (coin left right : Val rT)
    (encode : α → Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) μ encode)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) ν encode) :
    IsDistSpec (GF := GF) E pl(&Occil.mixture &coin.fst &left.fst &right.fst #())
      (law p μ ν) encode where
  spec F hF := wand_entails (twp_mixture E p coin left right encode hcoin hleft hright F hF)

end specification

end

end SampLib.Mixture
