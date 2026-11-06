import SampLib.Templates
import Samplers.General.Core
import SampLib.General.Laws.StoppedSum

/-! # Sums stopped at an independent natural count -/

open ProbLang
open scoped ENNReal

namespace SampLib.StoppedSum

noncomputable section

/-- The finite summation loop shared by stopped sums and episodes. -/
def sumLoop {rT : Type _} [ProbLangℝ rT] (sample : Val rT) : Exp rT :=
  .fix (.lam (pl% if {Exp.bvar 0} = #0 then #0 else
    &sample.fst #() + {Exp.bvar 1} ({Exp.bvar 0} - #1)))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Symbolic execution of a finite independent sum. -/
theorem twp_sumLoop (E : CoPset) (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (n : ℕ) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂sumLaw μ n) -∗
      tglWp E pl(&(sumLoop sample) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists (0 : ℤ)
    isimp only [sumLaw, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    iterate 5 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&(sumLoop sample) #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← sum_expectation μ n F] at Hcredit
      iapply IH $$ Hcredit
    iintro %v ⟨%rest, %hv, Hcredit⟩
    subst v
    twp_bind pl(&sample.fst #())
    iapply (hsample.wp (fun x => F (x + rest)) (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    twp_pures
    twp_value
    imodintro
    iexists x + rest
    iframe Hcredit
    itrivial

/-- Sample the stopping count, then execute its finite sum. -/
theorem twp_stoppedSum (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (counter sample : Val rT)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law ν μ) -∗
      tglWp E pl(&Occil.General.stoppedSum &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  have hloop := twp_sumLoop (rT := rT) (GF := GF) E μ sample hsample
  simp [sumLoop] at hloop
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&counter.fst #())
  isimp only [← expectation ν μ F] at Hcredit
  iapply (hcounter.wp (fun n => ∫⁻ z, F z ∂sumLaw μ n)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iterate 4 twp_pure
  iapply hloop n F
  iexact Hcredit

/-- Typed random-sum law for every probability distribution on natural counts. -/
theorem stoppedSum_distSpec (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (counter sample : Val rT)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int) :
    IsDistSpec (GF := GF) E pl(&Occil.General.stoppedSum &counter.fst &sample.fst #())
      (law ν μ) Val.int where
  spec F _ := wand_entails (twp_stoppedSum E ν μ counter sample hcounter hsample F)

end specification

end

end SampLib.StoppedSum
