import SampLib.General.Laws.SymmetricMetropolis
import SampLib.General.MetropolisKernel
import SampLib.General.Support.MetropolisTerms

/-! # Symmetric-proposal Metropolis iteration -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.SymmetricMetropolis

noncomputable section

private def unitRatio {rT : Type _} : Val rT :=
  ⟨pl(fun x y, (#1, #1)), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
local bi (IProp GF)

attribute [local pl_step_simp] MetropolisTerms.metropolisHastings_openRec
  MetropolisTerms.metropolisHastings_closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem unitRatio_spec (E : CoPset) (a b : Val rT) :
    ⊢ tglWp E pl(&(unitRatio (rT := rT)).fst &a.fst &b.fst)
      (fun v : Val rT => iprop(⌜v = Val.pair (Val.int 1) (Val.int 1)⌝)) := by
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

/-- The implemented finite-step kernel; symmetry identifies its invariant target. -/
theorem metropolis_distSpec (E : CoPset) (w : α → ℕ) (p : Metropolis.Proposal α)
    (encode : α → Val rT) (target proposal : Val rT)
    (htarget : ∀ x, ⊢ tglWp E pl(&target.fst &(encode x).fst)
      (fun v : Val rT => iprop(⌜v = Val.int (w x)⌝)))
    (hproposal : ∀ x, IsDistSpec (GF := GF) E pl(&proposal.fst &(encode x).fst)
      (Metropolis.proposal p x) encode)
    (n : ℕ) (x : α) (hx : 0 < w x) :
    IsDistSpec (GF := GF) E pl(&Occil.General.metropolis &target.fst &proposal.fst
      &(encode x).fst #int (n : ℤ)) (law w p n x) encode where
  spec F hF := by
    have hmodel := MetropolisRatio.kernel_distSpec E w ratios (Metropolis.proposal p)
      (by intro x; filter_upwards with y; simp [ratios]) encode target proposal unitRatio
      htarget (fun x y => unitRatio_spec E (encode x) (encode y)) hproposal n x hx
    have hnext := hmodel.spec F hF
    simp [unitRatio, Exp.close, Exp.closeRec] at hnext
    iintro Hcredit
    iterate 4 twp_pure
    iapply hnext $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero iterations return any initial value without invoking the callbacks. -/
theorem metropolis_zero_distSpec (E : CoPset) (target proposal initial : Val rT) :
    IsDistSpec (GF := GF) E pl(&Occil.General.metropolis &target.fst &proposal.fst
      &initial.fst #0) (MeasureTheory.Measure.dirac ()) (fun _ : Unit => initial) where
  spec F hF := by
    have hnext := (MetropolisRatio.zero_distSpec (GF := GF) E target proposal
      unitRatio initial).spec F hF
    simp [unitRatio, Exp.close, Exp.closeRec] at hnext
    iintro Hcredit
    iterate 4 twp_pure
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iapply hnext $$ Hcredit

end specification

end

end SampLib.SymmetricMetropolis
