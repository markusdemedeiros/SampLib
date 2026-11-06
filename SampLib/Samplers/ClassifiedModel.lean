import SampLib.GeneralSyntax
import SampLib.Samplers.Choice
import SampLib.Distributions.WeightedSupport
import SampLib.SupportedSpec
import Samplers.General.DataModels

/-! # A tagged mixture of supplied class-conditional models -/

open ProbLang
open scoped ENNReal

namespace SampLib.ClassifiedModel

noncomputable section

private theorem length_ne_zero (weights : List ℕ) [NeZero weights.sum] :
    weights.length ≠ 0 := by
  intro h
  have hz : weights = [] := List.eq_nil_of_length_eq_zero h
  simpa [hz] using NeZero.ne weights.sum

/-- Totalize the category index; the modular fallback is outside weighted support. -/
def position (weights : List ℕ) [NeZero weights.sum] (i : ℕ) : Fin weights.length :=
  letI : NeZero weights.length := ⟨length_ne_zero weights⟩
  Choice.position weights.length i

private theorem position_of_lt (weights : List ℕ) [NeZero weights.sum]
    (i : ℕ) (hi : i < weights.length) : position weights i = ⟨i, hi⟩ := by
  let : NeZero weights.length := ⟨length_ne_zero weights⟩
  exact Choice.position_of_lt i hi

section mathematics

open MeasureTheory

variable {α : Type _} [MeasurableSpace α]

/-- Keep the sampled class alongside its independent class-conditional observation. -/
def law (weights : List ℕ) [NeZero weights.sum] (μ : Fin weights.length → Measure α) :
    Measure (Fin weights.length × α) :=
  (WeightedChoice.law weights).bind
    (fun i => (μ (position weights i)).map (fun x => (position weights i, x)))

instance (weights : List ℕ) [NeZero weights.sum] (μ : Fin weights.length → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (law weights μ) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp

/-- Conditioning on the class gives the tagged mixture expectation. -/
theorem expectation (weights : List ℕ) [NeZero weights.sum]
    (μ : Fin weights.length → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (F : Fin weights.length × α → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ i, ∫⁻ x, F (position weights i, x) ∂μ (position weights i)
      ∂WeightedChoice.law weights = ∫⁻ p, F p ∂law weights μ := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable hF.aemeasurable]
  apply lintegral_congr
  intro i
  have hm : Measurable (fun x : α => (position weights i, x)) :=
    measurable_const.prodMk measurable_id
  rw [lintegral_map hF hm]

end mathematics

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
