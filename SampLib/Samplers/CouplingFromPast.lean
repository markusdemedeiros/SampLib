import SampLib.Distributions.CFTPWork
import SampLib.Syntax.CFTP
import SampLib.WeightedAmplification

/-! # Exact finite-state coupling from the past

The stored history is chronological and is retained when the horizon doubles.
Stationarity funds its output credit; a positive finite coalescent block supplies
a bounded remaining-round potential for termination.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal NNReal

namespace SampLib.CouplingFromPast

noncomputable section

private theorem cast_double (h : ℕ) : (h : ℤ) * 2 = ((h * 2 : ℕ) : ℤ) := by
  simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] applyMaps_openRec applyMaps_closeRec run_openRec
  ListOperations.append_openRec ListOperations.append_closeRec
  ListOperations.repeatSample_openRec ListOperations.repeatSample_closeRec

private abbrev post {n : ℕ} (F : Fin n → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ x : Fin n, ⌜v = stateVal x⌝ ∗ ↯ (F x))

/-- Execute the finite deterministic prefix of one CFTP round. -/
private theorem twp_run_head (E : CoPset) {n : ℕ} [NeZero n] (sample : Val rT)
    (h : ℕ) (maps : List (Map n)) (Φ : Val rT → IProp GF) :
    ⊢ (if Coalesces maps then Φ (stateVal (applyMaps maps 0))
      else tglWp E (extend sample h maps) Φ) -∗
      tglWp E pl(&(run n sample) #int (h : ℤ) &(mapsVal maps).fst) Φ := by
  classical
  have hn : n = 1 + (n - 1) := by have := NeZero.pos n; omega
  have hfirst := twp_applyMaps (rT := rT) (GF := GF) E maps (0 : Fin n)
  simp only [Fin.val_zero, Nat.cast_zero] at hfirst
  iintro Hcont
  iterate 3 twp_pure
  twp_bind pl(&Occil.General.applyMaps &(mapsVal maps).fst #0)
  iapply tglWp_wand
  isplitl []
  · iapply hfirst
  iintro %v %hv
  subst v
  twp_pure
  twp_pure
  twp_bind pl(&(allStates maps (applyMaps maps 0)) #1)
  iapply tglWp_wand
  isplitl []
  · iapply twp_allStates E maps (applyMaps maps 0) 1 (n - 1) hn
  iintro %v %hv
  subst v
  simp only [← coalesces_iff_agree]
  by_cases hc : Coalesces maps
  · isimp only [ite_eq_left hc] at Hcont
    rw [decide_eq_true hc]
    twp_pure
    iapply (tglWp_value_of_toVal (e := (stateVal (applyMaps maps 0) : Val rT).fst)
      (v := stateVal (applyMaps maps 0)) (by rfl))
    iexact Hcont
  · isimp only [ite_eq_right hc] at Hcont
    rw [decide_eq_false hc]
    twp_pure
    twp_bind (extend sample h maps)
    iapply (tglWp_mono fun _ => tglWp_value)
    iexact Hcont

private theorem twp_run_done (E : CoPset) {n : ℕ} [NeZero n]
    (π : Measure (Fin n)) [IsProbabilityMeasure π] (sample : Val rT)
    (h : ℕ) (maps : List (Map n)) (hc : Coalesces maps) (F : Fin n → ℝ≥0∞) :
    ⊢ ↯ (credit π maps F) -∗
      tglWp E pl(&(run n sample) #int (h : ℤ) &(mapsVal maps).fst) (post F) := by
  classical
  iintro Hcredit
  iapply twp_run_head E sample h maps (post F)
  rw [ite_eq_left hc]
  isimp only [credit_coalesces π maps hc 0 F] at Hcredit
  iexists applyMaps maps 0
  iframe Hcredit
  itrivial

private abbrev State (n : ℕ) := ℕ+ × List (Map n)

private theorem twp_weighted (E : CoPset) {n : ℕ} [NeZero n]
    (ρ : Measure (Map n)) [IsProbabilityMeasure ρ]
    (π : Measure (Fin n))
    [IsProbabilityMeasure π] (hπ : Stationary ρ π) (b : Block ρ) (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) ρ mapVal)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ∀ s : State n, ↯ (ε * b.work s.1.val) -∗
      ∀ F : Fin n → ℝ≥0∞, ↯ (credit π s.2 F) -∗
        tglWp E pl(&(run n sample) #int (s.1.val : ℤ) &(mapsVal s.2).fst) (post F) := by
  classical
  iapply ErrorCredit.Induction.weighted
    (fun s : State n => b.work s.1.val) (fun s => b.one_le_work s.1.val) _
    ε hε b.amplification b.one_lt_amplification $$ []
  iintro !> %ε %hε #IH %s Hterm %F Hcredit
  rcases s with ⟨h, maps⟩
  iapply twp_run_head E sample h.val maps (post F)
  by_cases hc : Coalesces maps
  · rw [ite_eq_left hc]
    isimp only [credit_coalesces π maps hc 0 F] at Hcredit
    iexists applyMaps maps 0
    iframe Hcredit
    itrivial
  · rw [ite_eq_right hc]
    twp_bind pl(&Occil.repeatSample &sample.fst #int (h.val : ℤ))
    icombine Hcredit Hterm as Htotal
    ihave Hsample := ErrorCredit.weaken
      (expectation ρ π hπ b h.val h.property maps F ε) $$ Htotal
    iapply ((repeatMaps_distSpec E ρ sample hsample h.val).wp
      (extensionCredit b π h.val maps F ε) (measurable_of_countable _) _) $$ Hsample
    iintro %older Hcredit
    twp_pure
    twp_bind pl(&Occil.General.append &(mapsVal older).fst &(mapsVal maps).fst)
    iapply tglWp_wand
    isplitl []
    · iapply ListOperations.twp_append E mapVal older maps
    iintro %v %hv
    subst v
    twp_pure
    rw [cast_double]
    twp_bind pl(&(run n sample) #int ((h.val * 2 : ℕ) : ℤ) &(mapsVal (older ++ maps)).fst)
    iapply (tglWp_mono fun _ => tglWp_value)
    by_cases hnew : Coalesces (older ++ maps)
    · isimp only [extensionCredit, ite_eq_left hnew, add_zero] at Hcredit
      iapply twp_run_done E π sample (h.val * 2) (older ++ maps) hnew F $$ Hcredit
    · isimp only [extensionCredit, ite_eq_right hnew] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      ispecialize IH $$
        %((⟨h.val * 2, Nat.mul_pos h.property (by decide)⟩, older ++ maps) : State n)
      isimp only [PNat.mk_coe] at IH
      iapply IH $$ Hterm %F Hcredit

private theorem twp_run (E : CoPset) {n : ℕ} [NeZero n]
    (ρ : Measure (Map n)) [IsProbabilityMeasure ρ]
    (π : Measure (Fin n))
    [IsProbabilityMeasure π] (hπ : Stationary ρ π) (b : Block ρ) (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) ρ mapVal)
    (h : ℕ) (hh : 0 < h) (maps : List (Map n)) (F : Fin n → ℝ≥0∞) :
    ⊢ ↯ (credit π maps F) -∗
      tglWp E pl(&(run n sample) #int (h : ℤ) &(mapsVal maps).fst) (post F) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  have hscaled : 0 < ε * (b.ceiling⁻¹ : ℝ≥0) :=
    ENNReal.mul_pos_iff.mpr ⟨hε, ENNReal.coe_pos.mpr (inv_pos.mpr b.ceiling_pos)⟩
  ihave Hterm := ErrorCredit.weaken (b.initial_work h ε) $$ Hterm
  ihave Hrun := (twp_weighted E ρ π hπ b sample hsample _ hscaled)
    $$ %((⟨h, hh⟩, maps) : State n)
  isimp only [PNat.mk_coe] at Hrun
  iapply Hrun $$ Hterm %F Hcredit

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem mapsVal_singleton {n : ℕ} (f : Map n) :
    pl(inr(({Exp.ofVal (mapVal f : Val rT)}, {Exp.ofVal (Val.inl Val.unit : Val rT)}))) =
      Exp.ofVal (mapsVal [f] : Val rT) := rfl

/-- Exact stationary sampling for every iid finite-map law with a positive finite
coalescent block. Existing histories are retained when the horizon doubles. -/
theorem couplingFromPast_distSpec (E : CoPset) {n : ℕ} [NeZero n]
    (ρ : Measure (Map n)) [IsProbabilityMeasure ρ]
    (π : Measure (Fin n))
    [IsProbabilityMeasure π] (hπ : Stationary ρ π)
    (hcoal : ∃ L, 0 < (IIDList.law ρ L) {maps | Coalesces maps}) (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) ρ mapVal) :
    IsDistSpec (GF := GF) E pl(&Occil.General.couplingFromPast #int (n : ℤ) &sample.fst #())
      π stateVal where
  spec F _ := by
    classical
    obtain ⟨b⟩ := Block.exists_iff.mpr hcoal
    have hn : ¬(n : ℤ) ≤ 0 := by have := NeZero.pos n; omega
    have hinit : (∫⁻ f, credit π [f] F ∂ρ) = ∫⁻ x, F x ∂π :=
      prepend_expectation ρ π hπ [] F
    iintro Hcredit
    iterate 4 twp_pure
    simp only [hn, _root_.decide_false]
    twp_pure
    twp_pure
    twp_bind pl(&sample.fst #())
    isimp only [← hinit] at Hcredit
    iapply (hsample.wp (fun f => credit π [f] F) (measurable_of_countable _) _) $$ Hcredit
    iintro %f Hcredit
    rw [mapsVal_singleton]
    twp_bind pl(&(run n sample) #1 &(mapsVal [f]).fst)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply twp_run E ρ π hπ b sample hsample 1 zero_lt_one [f] F $$ Hcredit

end specification

end

end SampLib.CouplingFromPast
