import SampLib.General.Laws.StoppedExtrema
import SampLib.Core.SupportedSpec
import Samplers.General.Core

/-! # Independently stopped maxima -/

open ProbLang
open scoped ENNReal

namespace SampLib.StoppedMaximum

noncomputable section

/-- Insert the callback after closing the loop's own binders. -/
private def loop {rT : Type _} (sample : Val rT) : Exp rT :=
  Exp.subst (pl% rec draw remaining current := if remaining = #0 then current else
    let x := source #();
    draw (remaining - #1) (if current < x then x else current)) (.named "source") sample.fst

private theorem positive_test (n : ℕ) (h : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by omega)

private theorem pred_cast (n : ℕ) (h : 0 < n) :
    (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (n : ℕ) (current : ℤ) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂StoppedExtrema.tailLaw false μ n current) -∗
      tglWp E pl(&(loop sample) #int (n : ℤ) #int current)
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  induction n generalizing current F with
  | zero =>
    iintro Hcredit
    isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
    twp_pures
    twp_value
    imodintro
    iexists current
    isimp only [StoppedExtrema.tailLaw_zero, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    simp [loop, Exp.subst, Exp.close, Exp.closeRec] at IH
    iintro Hcredit
    isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
    twp_pures
    twp_bind pl(&sample.fst #())
    isimp only [← StoppedExtrema.tail_expectation false μ n current F] at Hcredit
    iapply (hsample.wp (fun x => ∫⁻ z, F z ∂StoppedExtrema.tailLaw false μ n
      (StoppedExtrema.combine false current x)) (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    twp_pures
    by_cases h : current < x
    · rw [decide_eq_true h]
      iterate 2 twp_pure
      rw [add_sub_cancel_right]
      simp only [Exp.ofVal]
      isimp only [StoppedExtrema.combine_max, ite_eq_left h] at Hcredit
      iapply IH $$ Hcredit
    · rw [decide_eq_false h]
      iterate 2 twp_pure
      rw [add_sub_cancel_right]
      simp only [Exp.ofVal]
      isimp only [StoppedExtrema.combine_max, ite_eq_right h] at Hcredit
      iapply IH $$ Hcredit

theorem twp_stoppedMaximum (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (counter sample : Val rT)
    (hpositive : ∀ᵐ n ∂ν, 0 < n)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂StoppedExtrema.law false ν μ) -∗
      tglWp E pl(&Occil.General.stoppedMaximum &counter.fst &sample.fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E μ sample hsample
  simp [loop, Exp.subst, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&counter.fst #())
  isimp only [← StoppedExtrema.expectation false ν μ F] at Hcredit
  iapply (hcounter.wp_supported (fun n => 0 < n) (Set.to_countable _).measurableSet hpositive
    (fun n => ∫⁻ x, ∫⁻ z, F z ∂StoppedExtrema.tailLaw false μ (n - 1) x ∂μ)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n %hn Hcredit
  iterate 2 twp_pure
  rw [positive_test n hn]
  iterate 2 twp_pure
  twp_bind pl(&sample.fst #())
  iapply (hsample.wp (fun x => ∫⁻ z, F z ∂StoppedExtrema.tailLaw false μ (n - 1) x)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %x Hcredit
  twp_pure
  rw [pred_cast n hn]
  simp only [Exp.ofVal]
  iapply hloop (n - 1) x F
  iexact Hcredit

/-- Typed stopped extremum, for every almost-surely positive count law. -/
theorem stoppedMaximum_distSpec (E : CoPset) (ν : MeasureTheory.Measure ℕ)
    [MeasureTheory.IsProbabilityMeasure ν] (μ : MeasureTheory.Measure ℤ)
    [MeasureTheory.IsProbabilityMeasure μ] (counter sample : Val rT)
    (hpositive : ∀ᵐ n ∂ν, 0 < n)
    (hcounter : IsDistSpec (GF := GF) E pl(&counter.fst #()) ν (fun n => Val.int (n : ℤ)))
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ Val.int) :
    IsDistSpec (GF := GF) E pl(&Occil.General.stoppedMaximum &counter.fst &sample.fst #())
      (StoppedExtrema.law false ν μ) Val.int where
  spec F _ := wand_entails (twp_stoppedMaximum E ν μ counter sample hpositive hcounter hsample F)

end specification

end

end SampLib.StoppedMaximum
