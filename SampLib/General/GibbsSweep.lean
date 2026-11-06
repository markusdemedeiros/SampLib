import SampLib.General.Laws.FiniteKernels
import Samplers.General.Core

/-! # A sweep of conditional transition kernels

Each callback supplies the conditional law at the current state. Composition
gives the sweep law, and kernels preserving a common target preserve it jointly.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.GibbsSweep

noncomputable section

section mathematics

open MeasureTheory

abbrev law {α : Type _} [MeasurableSpace α] (K : ℕ → α → MeasureTheory.Measure α) (dimension : ℕ) :=
  FiniteKernels.sweep K 0 dimension

private theorem end_zero (i dimension : ℕ) (h : i + 0 = dimension) : i = dimension := by
  simpa only [Nat.add_zero] using h

private theorem index_lt_end (i n dimension : ℕ) (h : i + (n + 1) = dimension) :
    i < dimension := by omega

private theorem next_remaining (i n dimension : ℕ) (h : i + (n + 1) = dimension) :
    i + 1 + n = dimension := by omega

private theorem stop_test (dimension : ℕ) :
    decide ((dimension : ℤ) ≤ (dimension : ℤ)) = true := decide_eq_true le_rfl

private theorem continue_test (i n dimension : ℕ) (h : i + (n + 1) = dimension) :
    decide ((dimension : ℤ) ≤ (i : ℤ)) = false := decide_eq_false (by omega)

end mathematics

/-- Substitute the callback after closing the loop's own binders. -/
private def loop {rT : Type _} (dimension : ℕ) (conditional : Val rT) : Exp rT :=
  Exp.subst (pl% rec update index state := if #int (dimension : ℤ) <= index then state else
    update (index + #1) (conditional index state)) (.named "conditional") conditional.fst

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (dimension : ℕ) (conditional : Val rT)
    (encode : α → Val rT) (K : ℕ → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hconditional : ∀ i < dimension, ∀ x,
      IsDistSpec (GF := GF) E pl(&conditional.fst #int (i : ℤ) &(encode x).fst)
        (K i x) encode)
    (n i : ℕ) (hi : i + n = dimension) (x : α) (F : α → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂FiniteKernels.sweep K i n x) -∗
      tglWp E pl(&(loop dimension conditional) #int (i : ℤ) &(encode x).fst)
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z))) := by
  induction n generalizing i x F with
  | zero =>
    have heq := end_zero i dimension hi
    subst i
    isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
    iintro Hcredit
    twp_pures
    rw [stop_test]
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst (encode x)))
    iexists x
    isimp only [FiniteKernels.sweep, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    have hlt := index_lt_end i n dimension hi
    have htest := continue_test i n dimension hi
    isimp [loop, Exp.subst, Exp.close, Exp.closeRec]
    iintro Hcredit
    twp_pures
    rw [htest]
    twp_pures
    twp_bind pl(&conditional.fst #int (i : ℤ) &(encode x).fst)
    isimp only [← FiniteKernels.sweep_expectation K i n x F] at Hcredit
    iapply ((hconditional i hlt x).wp (fun y => ∫⁻ z, F z ∂FiniteKernels.sweep K (i + 1) n y)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %y Hcredit
    twp_pure
    rw [← Nat.cast_add_one]
    have hnext := ih (i + 1) (next_remaining i n dimension hi) y F
    simp [loop, Exp.subst, Exp.close, Exp.closeRec] at hnext
    exact wand_entails hnext

/-- A complete deterministic-order sweep of freshly sampled conditional kernels. -/
theorem twp_gibbsSweep (E : CoPset) (dimension : ℕ) (conditional : Val rT)
    (encode : α → Val rT) (K : ℕ → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hconditional : ∀ i < dimension, ∀ x,
      IsDistSpec (GF := GF) E pl(&conditional.fst #int (i : ℤ) &(encode x).fst)
        (K i x) encode)
    (x : α) (F : α → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law K dimension x) -∗
      tglWp E pl(&Occil.General.gibbsSweep #int (dimension : ℤ)
        &conditional.fst &(encode x).fst)
        (fun v : Val rT => iprop(∃ z : α, ⌜v = encode z⌝ ∗ ↯ (F z))) := by
  have hloop := twp_loop (GF := GF) E dimension conditional encode K hconditional
    dimension 0 (Nat.zero_add dimension) x F
  simp [loop, Exp.subst, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  iterate 6 twp_pure
  exact wand_entails hloop

/-- The normalized sweep law, including the identity sweep in dimension zero. -/
theorem gibbsSweep_distSpec (E : CoPset) (dimension : ℕ) (conditional : Val rT)
    (encode : α → Val rT) (K : ℕ → α → MeasureTheory.Measure α)
    [∀ i x, MeasureTheory.IsProbabilityMeasure (K i x)]
    (hconditional : ∀ i < dimension, ∀ x,
      IsDistSpec (GF := GF) E pl(&conditional.fst #int (i : ℤ) &(encode x).fst)
        (K i x) encode) (x : α) :
    IsDistSpec (GF := GF) E pl(&Occil.General.gibbsSweep #int (dimension : ℤ)
      &conditional.fst &(encode x).fst) (law K dimension x) encode where
  spec F _ := wand_entails
    (twp_gibbsSweep E dimension conditional encode K hconditional x F)

end specification

end

end SampLib.GibbsSweep
