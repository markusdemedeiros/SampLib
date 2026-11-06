import SampLib.Bernoulli.Support.EnvelopeConditionalAverage

open ProbLang

namespace ExactEnvelopeConditionalAverageCallers

open SampLib SampLib.FactoryFractions SampLib.EnvelopeConditionalAverage

noncomputable section

def raw (_ : ℕ) : Bool → Fraction
  | false => ⟨2, 6, by decide⟩
  | true => ⟨4, 6, by decide⟩

def callback {rT : Type} : Val rT :=
  ⟨pl(fun n j, ((#2, #6), (#4, #6))), .lam (by is_lc), by is_lc⟩

example : mean raw 1 2 0 false = 1 / 3 := by
  norm_num [mean, raw, Fraction.value, ReverseBinomial.coefficient_eq, Finset.sum_range_succ]
example : mean raw 1 2 1 false = 1 / 3 := by
  norm_num [mean, raw, Fraction.value, ReverseBinomial.coefficient_eq, Finset.sum_range_succ]
example : mean raw 1 2 2 true = 2 / 3 := by
  norm_num [mean, raw, Fraction.value, ReverseBinomial.coefficient_eq, Finset.sum_range_succ]
example : mean raw 0 1 0 true = 1 := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem callback_spec (E : CoPset) (n j : ℕ) :
    ⊢ tglWp E pl(&(callback (rT := rT)).fst #int (n : ℤ) #int (j : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.pair (raw j false).encode (raw j true).encode⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  rfl

/-- A caller may retain an arbitrary linear resource through the exact averaging closure. -/
example (E : CoPset) (n m k : ℕ) (high : Bool) (hnm : n ≤ m) (hkm : k ≤ m)
    (R : IProp GF) :
    R ⊢ tglWp E pl(&(conditionalClosure (callback (rT := rT)) n m k).fst &(Val.bool high).fst)
      (fun v : Val rT => iprop(⌜v = encode (mean raw n m k high)⌝ ∗ R)) := by
  iintro HR
  iapply tglWp_wand
  isplitl []
  · iapply twp_conditionalClosure E raw callback n m k high hnm hkm
      (fun _ j _ => callback_spec E n j)
  iintro %v %hv
  iframe HR
  itrivial

/-- The degree-zero shortcut does not invoke its callback, even when it is not a function. -/
example (E : CoPset) :
    ⊢ tglWp E pl(&(conditionalClosure (Val.unit : Val rT) 0 1 0).fst #true)
      (fun v : Val rT => iprop(⌜v = encode 1⌝)) := by
  have h := twp_conditionalClosure (rT := rT) (GF := GF) E raw (Val.unit : Val rT)
    0 1 0 true (by decide) (by decide) (by intro hn; omega)
  simpa only [mean, ite_true] using h

example (E : CoPset) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.choose #3 #(-1))
      (fun v : Val rT => iprop(⌜v = Val.int 0⌝)) := by
  have h := twp_choose_difference (rT := rT) (GF := GF) E 3 0 1
  simpa using h

#print axioms SampLib.EnvelopeConditionalAverage.twp_conditionalBody
#print axioms SampLib.EnvelopeConditionalAverage.twp_conditionalClosure
#print axioms SampLib.EnvelopeConditionalAverage.twp_choose_difference
#print axioms SampLib.EnvelopeConditionalAverage.opened_high

end specification

end

end ExactEnvelopeConditionalAverageCallers
