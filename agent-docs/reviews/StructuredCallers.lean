import SampLib.Continuous.Mixture
import Metrology.Iris.LocalBI
import SampLib.Continuous.UniformMin
import SampLib.Continuous.UniformMax
import SampLib.Continuous.UniformSum
import SampLib.Continuous.Rejection
import SampLib.Combinatorial.Choice
import SampLib.Bernoulli.ProbabilityGeneratingFactory
import SampLib.Bernoulli.LogisticFactory
import SampLib.Uniform.RealCoin
import SampLib.Combinatorial.SampleWithReplacement

/-!
# Independent structured-sampler caller checks

Reproducible API, resource-framing, boundary, duplicate-position, and infinity
checks from `review_structured` and the independent mathematical cross-review.
These declarations are checks, not additional verified samplers.
-/


section

open ProbLang
open scoped ENNReal
namespace StructuredReplacementReview
noncomputable section

open Iris Iris.ProofMode
open TotalEris ErisWpGS SampLib
open Iris.BI
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

-- The empty-input, zero-draw boundary needs no random-primitive assumption.
example (E : CoPset) (encode : α → Val rT) :
    IsDistSpec (GF := GF) E
      pl(&Occil.sampleWithReplacement &(listVal encode []).fst #int (0 : ℤ))
      (MeasureTheory.Measure.dirac ()) (fun _ : Unit => listVal encode []) :=
  SampleWithReplacement.sampleWithReplacement_zero_distSpec E encode []

example (E : CoPset) (encode : α → Val rT) :
    ⊢ tglWp E pl(&Occil.length &(listVal encode []).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (0 : ℤ)⌝)) :=
  twp_length E encode []

section random
variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (encode : α → Val rT) (xs : List α) [NeZero xs.length]
    (n : ℕ) (F : (Fin n → Fin xs.length) → ℝ≥0∞) (I : IProp GF) :
    ⊢ iprop(↯ (∫⁻ ys, F ys ∂SampleWithReplacement.law (Choice.law xs.length) n) ∗ I -∗
      tglWp E pl(let ys := &Occil.sampleWithReplacement &(listVal encode xs).fst
        #int (n : ℤ); ys)
        (fun v : Val rT => iprop(∃ ys : Fin n → Fin xs.length,
          ⌜v = listVal (fun i => encode (xs.get i)) (List.ofFn ys)⌝ ∗ ↯ (F ys) ∗ I))) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.sampleWithReplacement &(listVal encode xs).fst #int (n : ℤ))
  iapply ((SampleWithReplacement.sampleWithReplacement_distSpec E encode xs n).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %ys Hcredit
  twp_pures
  iapply (tglWp_value_of_toVal
    (e := (listVal (fun i => encode (xs.get i)) (List.ofFn ys)).fst)
    (v := listVal (fun i => encode (xs.get i)) (List.ofFn ys)) (Exp.toVal?_ofVal _))
  iexists ys
  iframe Hcredit HI
  itrivial

-- A singleton alphabet remains a valid input for every natural sample size.
example (E : CoPset) (encode : α → Val rT) (x : α) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.sampleWithReplacement &(listVal encode [x]).fst #int (n : ℤ))
      (SampleWithReplacement.law (Choice.law [x].length) n)
      (fun ys => listVal (fun i => encode ([x].get i)) (List.ofFn ys)) :=
  SampleWithReplacement.sampleWithReplacement_distSpec E encode [x] n
end random

end
end StructuredReplacementReview

end


section

open ProbLang
open scoped ENNReal
namespace StructuredReview
noncomputable section

open MeasureTheory in
example {α : Type _} [MeasurableSpace α] (μ ν : Measure α) :
    SampLib.Mixture.law 0 μ ν = ν := by
  simp [SampLib.Mixture.law, SampLib.RealCoin.pmf]

open MeasureTheory in
example {α : Type _} [MeasurableSpace α] (μ ν : Measure α) :
    SampLib.Mixture.law 1 μ ν = μ := by
  simp [SampLib.Mixture.law, SampLib.RealCoin.pmf]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] {μ ν : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (coin left right : Val rT)
    (encode : α → Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) μ encode)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) ν encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂Mixture.law p μ ν) ∗ I -∗
      tglWp E pl(let x := &Occil.mixture &coin.fst &left.fst &right.fst #(); x)
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.mixture &coin.fst &left.fst &right.fst #())
  iapply ((Mixture.mixture_distSpec E p coin left right encode hcoin hleft hright).wp F hF _)
    $$ Hcredit
  iintro %x Hcredit
  twp_pures
  iapply (tglWp_value_of_toVal (e := (encode x).fst) (v := encode x)
    (Exp.toVal?_ofVal _))
  iexists x
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open ProbLang
open scoped ENNReal
namespace StructuredReview
noncomputable section
open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂UniformMin.law) ∗ I -∗
      tglWp E pl(let x := &Occil.uniformMin #(); x)
        (fun v : Val ℝ => iprop(∃ x : ℝ, ⌜v = Val.real x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.uniformMin #())
  iapply ((UniformMin.uniformMin_distSpec E).wp F hF _) $$ Hcredit
  iintro %x Hcredit
  twp_pures
  twp_value
  imodintro
  iexists x
  iframe Hcredit HI
  itrivial

example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂UniformMax.law) ∗ I -∗
      tglWp E pl(let x := &Occil.uniformMax #(); x)
        (fun v : Val ℝ => iprop(∃ x : ℝ, ⌜v = Val.real x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.uniformMax #())
  iapply ((UniformMax.uniformMax_distSpec E).wp F hF _) $$ Hcredit
  iintro %x Hcredit
  twp_pures
  twp_value
  imodintro
  iexists x
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open Set
namespace StructuredReview
example : SampLib.UniformMin.law (Ioi (0 : ℝ)) = 1 := by
  simpa using SampLib.UniformMin.survival 0
example : SampLib.UniformMin.law (Ioi (1 : ℝ)) = 0 := by
  simpa using SampLib.UniformMin.survival 1
example : SampLib.UniformMax.law (Iic (0 : ℝ)) = 0 := by
  simpa using SampLib.UniformMax.cdf 0
example : SampLib.UniformMax.law (Iic (1 : ℝ)) = 1 := by
  simpa using SampLib.UniformMax.cdf 1
end StructuredReview

end

section

open ProbLang
open scoped ENNReal
namespace StructuredReview
noncomputable section

open MeasureTheory in
example : SampLib.UniformSum.law 0 = Measure.dirac 0 := rfl

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

example (E : CoPset) (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂UniformSum.law n) ∗ I -∗
      tglWp E pl(let x := &Occil.uniformSum #int (n : ℤ); x)
        (fun v : Val ℝ => iprop(∃ x : ℝ, ⌜v = Val.real x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.uniformSum #int (n : ℤ))
  iapply ((UniformSum.uniformSum_distSpec E n).wp F hF _) $$ Hcredit
  iintro %x Hcredit
  twp_pures
  twp_value
  imodintro
  iexists x
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open ProbLang Set
open scoped ENNReal
namespace StructuredReview
noncomputable section

open MeasureTheory in
example {α : Type _} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    SampLib.Rejection.law μ univ (by simp) = μ := by simp [SampLib.Rejection.law]

abbrev acceptTrue {rT : Type _} [ProbLangℝ rT] : Val rT :=
  ⟨pl(fun x, #true), .lam (by is_lc), by is_lc⟩

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ]
local bi (IProp GF)

-- Compose the public spec at acceptance mass one, including a concrete callback.
example (E : CoPset) (encode : α → Val rT) (proposal : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode) :
    IsDistSpec (GF := GF) E pl(&Occil.rejection &proposal.fst &(acceptTrue : Val rT).fst #())
      (Rejection.law μ univ (by simp)) encode := by
  apply Rejection.rejection_distSpec E μ univ MeasurableSet.univ (by simp) encode
    proposal acceptTrue hproposal
  intro x
  twp_pures
  twp_value
  imodintro
  itrivial

example (E : CoPset) (s : Set α) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hmass : μ s ≠ 0) (encode : α → Val rT)
    (proposal accept : Val rT)
    (hproposal : IsDistSpec (GF := GF) E pl(&proposal.fst #()) μ encode)
    (haccept : ∀ x, ⊢ tglWp E pl(&accept.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (x ∈ s))⌝)))
    (F : α → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (Rejection.credit μ s hmass F) ∗ I -∗
      tglWp E pl(let x := &Occil.rejection &proposal.fst &accept.fst #(); x)
        (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.rejection &proposal.fst &accept.fst #())
  isimp only [Rejection.credit] at Hcredit
  iapply ((Rejection.rejection_distSpec E μ s hs hmass encode proposal accept
    hproposal haccept).wp F hF _) $$ Hcredit
  iintro %x Hcredit
  twp_pures
  iapply (tglWp_value_of_toVal (e := (encode x).fst) (v := encode x) (Exp.toVal?_ofVal _))
  iexists x
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open ProbLang
open scoped ENNReal
namespace StructuredReview
noncomputable section

-- The repeated false entries retain their two positions; true gets one third.
example : (∫⁻ i : Fin 3, if ([false, false, true] : List Bool).get i then 1 else 0
    ∂SampLib.Choice.law 3) = (1 : ℝ≥0∞) / 3 := by
  rw [SampLib.Choice.lintegral_law]
  norm_num [SampLib.Choice.position, Finset.sum_range_succ]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

example (E : CoPset) (encode : α → Val rT) (xs : List α) [NeZero xs.length]
    (F : Fin xs.length → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ i, F i ∂Choice.law xs.length) ∗ I -∗
      tglWp E pl(let x := &Occil.choice &(listVal encode xs).fst; x)
        (fun v : Val rT => iprop(∃ i : Fin xs.length,
          ⌜v = encode (xs.get i)⌝ ∗ ↯ (F i) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.choice &(listVal encode xs).fst)
  iapply ((Choice.choice_distSpec E encode xs).wp F (measurable_of_countable _) _)
    $$ Hcredit
  iintro %i Hcredit
  twp_pures
  iapply (tglWp_value_of_toVal (e := (encode (xs.get i)).fst) (v := encode (xs.get i))
    (Exp.toVal?_ofVal _))
  iexists i
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open scoped ENNReal
example (F : Fin 1 → ℝ≥0∞) : (∫⁻ i, F i ∂SampLib.Choice.law 1) = F 0 := by
  rw [SampLib.Choice.lintegral_law]
  simp [SampLib.Choice.position]

end

section

open ProbLang
open scoped ENNReal
namespace StructuredReview
noncomputable section

open MeasureTheory in
example (p : unitInterval) (n : ℕ) :
    SampLib.ProbabilityGeneratingFactory.law (Measure.dirac n) p =
      SampLib.IterateCoin.law p n := by
  rw [SampLib.ProbabilityGeneratingFactory.law,
    Measure.dirac_bind (measurable_of_countable _) n]


open MeasureTheory in
example (ν : Measure ℕ) (p : unitInterval) :
    SampLib.ProbabilityGeneratingFactory.law ν p {true} =
      ∫⁻ n, ENNReal.ofReal ((p : ℝ) ^ n) ∂ν := by
  rw [SampLib.ProbabilityGeneratingFactory.law,
    Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  simp [SampLib.IterateCoin.law, SampLib.IterateCoin.bias,
    SampLib.RealCoin.law, SampLib.RealCoin.pmf]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (p : unitInterval) (coin count : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcount : IsDistSpec (GF := GF) E pl(&count.fst #()) ν (fun n => Val.int (n : ℤ)))
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂ProbabilityGeneratingFactory.law ν p) ∗ I -∗
      tglWp E pl(let b := &Occil.probabilityGeneratingFactory &coin.fst &count.fst #(); b)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.probabilityGeneratingFactory &coin.fst &count.fst #())
  iapply ((ProbabilityGeneratingFactory.probabilityGeneratingFactory_distSpec E ν p
    coin count hcoin hcount).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  twp_value
  imodintro
  iexists b
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open MeasureTheory Measure Set
open scoped ENNReal
namespace StructuredReview
noncomputable section
open SampLib

example (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    ProbabilityGeneratingFactory.law ν 0 {true} = ν {0} := by
  rw [ProbabilityGeneratingFactory.law,
    Measure.bind_apply (measurableSet_singleton _) (measurable_of_countable _).aemeasurable]
  have h : (fun n => IterateCoin.law 0 n {true}) =
      ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext n
    cases n <;> simp [IterateCoin.law, IterateCoin.bias, RealCoin.law, RealCoin.pmf]
  rw [h, lintegral_indicator_const (measurableSet_singleton _)]
  simp

example (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    ProbabilityGeneratingFactory.law ν 1 = Measure.dirac true := by
  have h : IterateCoin.law 1 = fun _ => (Measure.dirac true : Measure Bool) := by
    funext n
    simp [IterateCoin.law, IterateCoin.bias, RealCoin.law, RealCoin.pmf]
  rw [ProbabilityGeneratingFactory.law, h]
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  simp
end
end StructuredReview

end

section

open ProbLang
open scoped ENNReal
namespace StructuredReview
noncomputable section

example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    SampLib.LogisticFactory.integerBias 0 x y hx hy = 0 := by
  apply Subtype.ext
  simp [SampLib.LogisticFactory.integerBias]

example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    (SampLib.LogisticFactory.integerBias 1 x y hx hy : ℝ) =
      (x : ℝ) / ((x + y : ℤ) : ℝ) := by
  simp [SampLib.LogisticFactory.integerBias, add_comm]

example (p : unitInterval) :
    (SampLib.LogisticFactory.integerBias p 1 1 (by decide) (by decide) : ℝ) =
      (p : ℝ) / (1 + (p : ℝ)) := by
  simp [SampLib.LogisticFactory.integerBias]

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (p : unitInterval) (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (LogisticFactory.integerBias p x y hx hy)) ∗ I -∗
      tglWp E pl(let b := &Occil.logisticFactory &coin.fst #int x #int y #(); b)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  twp_bind pl(&Occil.logisticFactory &coin.fst #int x #int y #())
  iapply ((LogisticFactory.logisticFactory_distSpec E p x y hx hy coin hcoin).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  twp_value
  imodintro
  iexists b
  iframe Hcredit HI
  itrivial

end
end StructuredReview

end

section

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

noncomputable section

section mathematics
open MeasureTheory Measure
open SampLib

-- The inactive branch may carry infinite credit at an endpoint selector.
example : (∫⁻ b, (if b then ∞ else 1) ∂Mixture.law 0 (dirac true) (dirac false)) = 1 := by
  simp [Mixture.expectation_preservation, RealCoin.credit, RealCoin.pmf]

example : (∫⁻ b, (if b then 1 else ∞) ∂Mixture.law 1 (dirac true) (dirac false)) = 1 := by
  simp [Mixture.expectation_preservation, RealCoin.credit, RealCoin.pmf]

example : UniformMin.law (Ioi 0) = 1 := by simpa using UniformMin.survival 0
example : UniformMin.law (Ioi 1) = 0 := by simpa using UniformMin.survival 1
example : UniformMax.law (Iic 0) = 0 := by simpa using UniformMax.cdf 0
example : UniformMax.law (Iic 1) = 1 := by simpa using UniformMax.cdf 1

-- Infinite credit on a null endpoint stays null, including at the integral level.
example : (∫⁻ x, ({0} : Set ℝ).indicator (fun _ => ∞) x ∂UniformMax.law) = 0 := by
  have hnull : UniformMax.law ({0} : Set ℝ) = 0 := by
    apply measure_mono_null (s := ({0} : Set ℝ)) (t := Iic 0)
    · simp [subset_def]
    · simpa using UniformMax.cdf 0
  rw [lintegral_indicator_const (measurableSet_singleton _), hnull, mul_zero]

example : (∫⁻ x, UniformMin.credit (fun _ => ∞) x ∂unifUnit) = ∞ := by
  rw [UniformMin.expectation_preservation _ measurable_const]
  simp

example : (∫⁻ x, UniformMax.credit (fun _ => ∞) x ∂unifUnit) = ∞ := by
  rw [UniformMax.expectation_preservation _ measurable_const]
  simp

example (n : ℕ) : (∫⁻ x, UniformSum.credit n (fun _ => ∞) x ∂unifUnit) = ∞ := by
  rw [UniformSum.expectation_preservation _ _ measurable_const]
  simp

example : (∫⁻ x, (if x = 1 then ∞ else 0) ∂UniformSum.law 0) = 0 := by
  simp [UniformSum.law]

example : (∫⁻ x, (if x = 0 then ∞ else 0) ∂UniformSum.law 0) = ∞ := by
  simp [UniformSum.law]

example : UniformSum.law 1 = unifUnit := by
  simp only [UniformSum.law, Measure.prod_dirac]
  have hsum : Measurable (fun z : ℝ × ℝ => z.1 + z.2) :=
    measurable_fst.add measurable_snd
  have hpair : Measurable (fun x : ℝ => (x, (0 : ℝ))) := measurable_prodMk_right
  rw [Measure.map_map hsum hpair]
  simp [Function.comp_def]

end mathematics

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS SampLib
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

-- A caller can retain unrelated resources through the recursive sum sampler.
example (E : CoPset) (n : ℕ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂UniformSum.law n) ∗ I -∗
      tglWp E pl(&Occil.uniformSum #int (n : ℤ))
        (fun v : Val ℝ => iprop(∃ x : ℝ, ⌜v = Val.real x⌝ ∗ ↯ (F x) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((UniformSum.uniformSum_distSpec E n).wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HI
  itrivial

end

end

section

open Set ProbLang MeasureTheory Measure
open scoped ENNReal
noncomputable section
namespace RejectionInfiniteAudit
def fair : unitInterval := ⟨1/2, by norm_num⟩
example : SampLib.RealCoin.law fair {true} ≠ 0 := by
  norm_num [SampLib.RealCoin.law, SampLib.RealCoin.pmf, fair]
example : SampLib.Rejection.law (SampLib.RealCoin.law fair) {true}
    (by norm_num [SampLib.RealCoin.law, SampLib.RealCoin.pmf, fair]) = dirac true := by
  norm_num [SampLib.Rejection.law, SampLib.RealCoin.law, SampLib.RealCoin.pmf, fair,
    smul_smul]
  rw [ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofReal_ne_top, one_smul]
example : SampLib.Rejection.credit (SampLib.RealCoin.law fair) {true}
    (by norm_num [SampLib.RealCoin.law, SampLib.RealCoin.pmf, fair])
    (fun b => if b then 0 else ∞) = 0 := by
  norm_num [SampLib.Rejection.credit, SampLib.Rejection.law, SampLib.RealCoin.law,
    SampLib.RealCoin.pmf, fair, smul_smul]
end RejectionInfiniteAudit

end

section

open Set ProbLang MeasureTheory Measure
open scoped ENNReal
noncomputable section
namespace LogisticCrossAudit
open SampLib LogisticFactory
example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    integerBias 0 x y hx hy = (0 : unitInterval) := by
  apply Subtype.ext
  simp [integerBias]
example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    (integerBias 1 x y hx hy : ℝ) = (x : ℝ) / ((x + y : ℤ) : ℝ) := by
  simp [integerBias, add_comm]
example (p : unitInterval) :
    (integerBias p 1 1 (by norm_num) (by norm_num) : ℝ) = (p : ℝ) / (1 + (p : ℝ)) := by
  simp [integerBias]
example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    RealCoin.law (integerBias 0 x y hx hy) = dirac false := by
  simp [RealCoin.law, RealCoin.pmf, integerBias]
example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    RealCoin.credit (integerBias 0 x y hx hy) (fun b => if b then ∞ else 0) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, integerBias]

def half : unitInterval := ⟨1/2, by norm_num⟩
example : (∫⁻ b, selectorCredit 0 half (by norm_num [half])
      (fun b => if b then ∞ else 0) 0 b ∂RealCoin.law half) ≤ 0 := by
  have h := expectation_preservation 0 half (by norm_num [half]) (by norm_num [half])
    (fun b => if b then ∞ else 0) 0
  simpa [credit, RealCoin.credit, RealCoin.pmf, bias] using h

end LogisticCrossAudit

end


section

open Set MeasureTheory Measure
open scoped ENNReal
namespace StructuredReplacementMath
noncomputable section
open SampLib

example : (∫⁻ ys : Fin 2 → Fin 3,
    if ([false, false, true] : List Bool).get (ys 0) &&
      ([false, false, true] : List Bool).get (ys 1) then 1 else 0
    ∂SampleWithReplacement.law (Choice.law 3) 2) = (1 : ℝ≥0∞) / 9 := by
  rw [SampleWithReplacement.lintegral_law_succ (Choice.law 3) 1 _ (measurable_of_countable _)]
  simp_rw [SampleWithReplacement.lintegral_law_succ (Choice.law 3) 0 _
    (measurable_of_countable _)]
  simp only [SampleWithReplacement.law, lintegral_dirac]
  simp_rw [Choice.lintegral_law]
  simp only [Choice.position, Finset.sum_range_succ]
  norm_num only [Fin.cons_zero, Fin.cons_succ, List.get_eq_getElem,
    List.getElem_cons_zero, List.getElem_cons_succ, Nat.reduceMod,
    Bool.false_and, Bool.true_and, Finset.sum_range_zero, add_zero, zero_add,
    zero_div, one_div]
  rw [show (9 : ℝ≥0∞) = (3 : ℝ≥0∞) ^ 2 by norm_num, ENNReal.inv_pow, pow_two]
  norm_num [div_eq_mul_inv]
end
end StructuredReplacementMath

end
