import SampLib.Core.GeneralSyntax
import SampLib.Combinatorial.Choice
import SampLib.Common.Laws.WeightedSupport
import SampLib.Core.SupportedSpec
import Samplers.General.DataModels
import SampLib.General.Laws.ClassifiedModel

/-! # A tagged mixture of supplied class-conditional models -/

open ProbLang
open scoped ENNReal

namespace SampLib.ClassifiedModel

noncomputable section

def encode {rT : Type _} {α : Type _} {n : ℕ}
    (output : α → Val rT) (p : Fin n × α) : Val rT :=
  .pair (.int (p.1.val : ℤ)) (output p.2)

private theorem encode_pair {rT : Type _} [ProbLangℝ rT] {α : Type _} {n : ℕ}
    (output : α → Val rT) (i : Fin n) (x : α) :
    pl((#int (i.val : ℤ), {Exp.ofVal (output x)})) =
      Exp.ofVal (encode output (i, x)) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_modelAt (E : CoPset) {n : ℕ} (models : Fin n → Val rT) (i : Fin n) :
    ⊢ tglWp E pl(&Occil.getAt &(listVal id (List.ofFn models)).fst #int (i.val : ℤ))
      (fun v : Val rT => iprop(⌜v = models i⌝)) := by
  simpa only [List.get_eq_getElem, List.getElem_ofFn, id_eq] using
    twp_getAt E id (List.ofFn models) ⟨i.val, by simp⟩

/-- Execute class selection, model lookup, and the selected callback. -/
theorem twp_classifiedModel (E : CoPset) (weights : List ℕ) [NeZero weights.sum]
    (μ : Fin weights.length → MeasureTheory.Measure α)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] (output : α → Val rT)
    (models : Fin weights.length → Val rT)
    (hmodels : ∀ i, IsDistSpec (GF := GF) E pl(&(models i).fst #()) (μ i) output)
    (F : Fin weights.length × α → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ p, F p ∂law weights μ) -∗
      tglWp E pl(&Occil.General.classifiedModel
        &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst
        &(listVal id (List.ofFn models)).fst #())
        (fun v : Val rT => iprop(∃ p : Fin weights.length × α,
          ⌜v = encode output p⌝ ∗ ↯ (F p))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [GeneralSyntax.length_openRec, GeneralSyntax.length_closeRec,
    MarkovTerms.weightedChoice_openRec, MarkovTerms.weightedChoice_closeRec,
    MarkovTerms.getAt_openRec, MarkovTerms.getAt_closeRec]
  twp_bind pl(&Occil.length &(listVal id (List.ofFn models)).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E id (List.ofFn models)
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.length &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E _ weights
  iintro %v %hv
  subst v
  simp only [List.length_ofFn]
  twp_pure
  rw [beq_self_eq_true]
  twp_pure
  twp_bind pl(&Occil.weightedChoice
    &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst)
  isimp only [← expectation weights μ F hF] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E weights).wp_supported
    (fun i => i < weights.length) (Set.to_countable _).measurableSet
    (WeightedChoice.ae_lt_length weights)
    (fun i => ∫⁻ x, F (position weights i, x) ∂μ (position weights i))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %i %hi Hcredit
  isimp only [position_of_lt weights i hi] at Hcredit
  twp_pure
  twp_bind pl(&Occil.getAt &(listVal id (List.ofFn models)).fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_modelAt E models ⟨i, hi⟩
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&(models ⟨i, hi⟩).fst #())
  iapply ((hmodels ⟨i, hi⟩).wp (fun x => F (⟨i, hi⟩, x))
    (hF.comp (measurable_const.prodMk measurable_id)) _) $$ Hcredit
  iintro %x Hcredit
  rw [encode_pair output (⟨i, hi⟩ : Fin weights.length) x]
  iapply (tglWp_value (v := encode output (⟨i, hi⟩, x)))
  iexists (⟨i, hi⟩, x)
  iframe Hcredit
  itrivial

/-- Typed tagged-mixture specification for a finite supplied model family. -/
theorem classifiedModel_distSpec (E : CoPset) (weights : List ℕ) [NeZero weights.sum]
    (μ : Fin weights.length → MeasureTheory.Measure α)
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] (output : α → Val rT)
    (models : Fin weights.length → Val rT)
    (hmodels : ∀ i, IsDistSpec (GF := GF) E pl(&(models i).fst #()) (μ i) output) :
    IsDistSpec (GF := GF) E pl(&Occil.General.classifiedModel
      &(listVal (fun w : ℕ => Val.int (w : ℤ)) weights).fst
      &(listVal id (List.ofFn models)).fst #()) (law weights μ) (encode output) where
  spec F hF := wand_entails (twp_classifiedModel E weights μ output models hmodels F hF)

end specification

end

end SampLib.ClassifiedModel
