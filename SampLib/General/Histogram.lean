import SampLib.Core.GeneralSyntax
import SampLib.Discrete.WeightedChoice
import SampLib.Uniform.RndIntExcRange
import SampLib.Common.Laws.WeightedSupport
import SampLib.General.Laws.Histogram
import SampLib.Core.SupportedSpec
import Samplers.General.DataModels

/-! # Histogram sampling with integer bin masses -/

open ProbLang
open scoped ENNReal

namespace SampLib.Histogram

noncomputable section

private theorem getD_eq_get (xs : List ℤ) (i : ℕ) (hi : i < xs.length) :
    xs[i]?.getD 0 = xs.get ⟨i, hi⟩ := by
  simp [List.getElem?_eq_getElem hi]

private theorem bin_bounds (points : List ℤ) (weights : List ℕ)
    (hlen : points.length = weights.length + 1) (i : ℕ) (hi : i < weights.length) :
    i < points.length ∧ i + 1 < points.length := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_getAtD (E : CoPset) (xs : List ℤ) (i : ℕ) (hi : i < xs.length) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) xs).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (xs[i]?.getD 0)⌝)) := by
  simpa only [getD_eq_get xs i hi] using twp_getAt E (fun z : ℤ => Val.int z) xs ⟨i, hi⟩

/-- Choose a bin by its mass, then sample its integer interval uniformly. -/
theorem twp_histogram (E : CoPset) (points : List ℤ) (weights : List ℕ)
    [NeZero weights.sum] (hlen : points.length = weights.length + 1)
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law points weights hwidth) -∗
      tglWp E pl(&Occil.General.histogram &(listVal (fun z : ℤ => Val.int z) points).fst
        &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
    MarkovTerms.weightedChoice_openRec, MarkovTerms.weightedChoice_closeRec,
    MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec,
    GeneralSyntax.rndIntExcRange_openRec, GeneralSyntax.rndIntExcRange_closeRec]
  twp_bind pl(&Occil.length &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ weights
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.length &(listVal (fun z : ℤ => Val.int z) points).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ points
  iintro %v %hv
  subst v
  simp only [hlen, Nat.cast_add_one]
  twp_pure
  rw [beq_self_eq_true]
  twp_pure
  twp_bind pl(&Occil.weightedChoice &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst)
  isimp only [← expectation points weights hwidth F] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E weights).wp_supported
    (fun i => i < weights.length) (Set.to_countable _).measurableSet
    (WeightedChoice.ae_lt_length weights)
    (fun i => ∫⁻ z, F z ∂binLaw points weights hwidth i)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i %hi Hcredit
  obtain ⟨hlo, hhi⟩ := bin_bounds points weights hlen i hi
  twp_pure
  twp_bind pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) points).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAtD E points i hlo
  iintro %v %hv
  subst v
  twp_pure
  twp_pure
  rw [← Nat.cast_add_one]
  twp_bind pl(&Occil.getAt &(listVal (fun z : ℤ => Val.int z) points).fst
    #int ((i + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_getAtD E points (i + 1) hhi
  iintro %v %hv
  subst v
  twp_pure
  isimp only [binLaw, dite_eq_left hi] at Hcredit
  simp only [GeneralSyntax.rndIntExcRange_openRec]
  iapply RndIntExcRange.twp_rndIntExcRange E _ _ (hwidth i hi) F
  iexact Hcredit

/-- Typed histogram law for nonnegative masses of positive total and valid bins. -/
theorem histogram_distSpec (E : CoPset) (points : List ℤ) (weights : List ℕ)
    [NeZero weights.sum] (hlen : points.length = weights.length + 1)
    (hwidth : ∀ i, i < weights.length → points[i]?.getD 0 < points[i + 1]?.getD 0) :
    IsDistSpec (GF := GF) E pl(&Occil.General.histogram
      &(listVal (fun z : ℤ => Val.int z) points).fst
      &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst #())
      (law points weights hwidth) Val.int where
  spec F _ := wand_entails (twp_histogram E points weights hlen hwidth F)

end specification

end

end SampLib.Histogram
