import SampLib.Distributions.CouplingFromPast
import SampLib.ListEncoding
import SampLib.ListOperations
import SampLib.DistributionMap

/-! # Stored maps and deterministic CFTP checks

Finite maps are encoded by their destination lists. Applying a stored history
and checking all its images consume no probabilistic credit.
-/

open ProbLang

namespace SampLib.CouplingFromPast

noncomputable section

def stateVal {rT : Type _} {n : ℕ} (x : Fin n) : Val rT := .int (x.val : ℤ)

def mapVal {rT : Type _} [ProbLangℝ rT] {n : ℕ} (f : Map n) : Val rT :=
  listVal stateVal (List.ofFn f)

abbrev mapsVal {rT : Type _} [ProbLangℝ rT] {n : ℕ} (maps : List (Map n)) : Val rT :=
  listVal mapVal maps

theorem applyMaps_lc {rT : Type _} :
    (Occil.General.applyMaps : Exp rT).IsLocallyClosed := by is_lc

theorem applyMaps_fv {rT : Type _} : (Occil.General.applyMaps : Exp rT).fv = ∅ := by
  rfl

theorem applyMaps_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.applyMaps = Occil.General.applyMaps :=
  (Exp.open_lc k e _ applyMaps_lc).symm

theorem applyMaps_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.applyMaps : Exp rT) = Occil.General.applyMaps :=
  Exp.closeRec_fresh x _ k (by simp [applyMaps_fv])

/-- Agreement with the proposed image on all unvisited states. -/
abbrev AgreeFrom {n : ℕ} (maps : List (Map n)) (first : Fin n) (j : ℕ) : Prop :=
  ∀ x : Fin n, j ≤ x.val → applyMaps maps x = first

private theorem agreeFrom_step {n : ℕ} (maps : List (Map n)) (first : Fin n)
    (j : ℕ) (hj : j < n) :
    AgreeFrom maps first j ↔ applyMaps maps ⟨j, hj⟩ = first ∧
      AgreeFrom maps first (j + 1) := by
  constructor
  · intro h
    exact ⟨h _ le_rfl, fun x hx => h x (by omega)⟩
  · rintro ⟨hj', ht⟩ x hx
    by_cases he : x.val = j
    · have hx' : x = ⟨j, hj⟩ := Fin.ext he
      simpa only [hx'] using hj'
    · exact ht x (by omega)

private theorem agreeFrom_end {n : ℕ} (maps : List (Map n)) (first : Fin n) :
    AgreeFrom maps first n := fun x hx => (not_lt_of_ge hx x.isLt).elim

theorem coalesces_iff_agree {n : ℕ} [NeZero n] (maps : List (Map n)) :
    Coalesces maps ↔ AgreeFrom maps (applyMaps maps 0) 1 := by
  constructor
  · exact fun h x _ => h x 0
  · intro h
    have hx (x : Fin n) : applyMaps maps x = applyMaps maps 0 := by
      by_cases he : x.val = 0
      · have hx' : x = 0 := Fin.ext he
        rw [hx']
      · exact h x (by omega)
    exact fun x y => (hx x).trans (hx y).symm

@[pl_fold] def allStates {rT : Type _} [ProbLangℝ rT] {n : ℕ} (maps : List (Map n))
    (first : Fin n) : Exp rT :=
  .fix (.lam (.cond (.binop .le (.lit (.int n)) (.bvar 0)) (.lit (.bool true))
    (.cond (.binop .eq
      (.app (.app Occil.General.applyMaps (mapsVal maps).fst) (.bvar 0))
      (stateVal first).fst)
      (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))) (.lit (.bool false)))))

private theorem state_beq {rT : Type _} [ProbLangℝ rT] {n : ℕ} (x y : Fin n) :
    ((BaseLit.int (x.val : ℤ) : BaseLit rT) == .int (y.val : ℤ)) = decide (x = y) := by
  change ((x.val : ℤ) == (y.val : ℤ)) = decide (x = y)
  simp [beq_eq_decide, Fin.ext_iff]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] applyMaps_openRec applyMaps_closeRec

theorem twp_getMap (E : CoPset) {n : ℕ} (f : Map n) (x : Fin n) :
    ⊢ tglWp E pl(&Occil.getAt &(mapVal f).fst #int (x.val : ℤ))
      (fun v : Val rT => iprop(⌜v = stateVal (f x)⌝)) := by
  have h := twp_getAt (GF := GF) E (stateVal (rT := rT)) (List.ofFn f)
    ⟨x.val, by simpa only [List.length_ofFn] using x.isLt⟩
  simpa [mapVal, List.get_eq_getElem] using h

theorem twp_applyMaps (E : CoPset) {n : ℕ} (maps : List (Map n)) (x : Fin n) :
    ⊢ tglWp E pl(&Occil.General.applyMaps &(mapsVal maps).fst #int (x.val : ℤ))
      (fun v : Val rT => iprop(⌜v = stateVal (applyMaps maps x)⌝)) := by
  induction maps generalizing x with
  | nil =>
    simp only [mapsVal, listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons f fs IH =>
    simp only [mapsVal, listVal]
    iterate 6 twp_pure
    twp_bind pl(&Occil.getAt &(mapVal f).fst #int (x.val : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_getMap E f x
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(&Occil.General.applyMaps &(mapsVal fs).fst #int ((f x).val : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    simp only [applyMaps_cons]
    iapply IH (f x)

/-- A complete finite-state agreement check, retaining the caller's resources. -/
theorem twp_allStates (E : CoPset) {n : ℕ} (maps : List (Map n)) (first : Fin n)
    (j r : ℕ) (hn : n = j + r) :
    ⊢ tglWp E pl(&(allStates maps first) #int (j : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.bool (decide (AgreeFrom maps first j))⌝)) := by
  classical
  induction r generalizing j with
  | zero =>
    have hle : (n : ℤ) ≤ (j : ℤ) := by omega
    have hagree : AgreeFrom maps first j := by simpa [hn] using agreeFrom_end maps first
    iterate 3 twp_pure
    simp only [hle, _root_.decide_true]
    twp_pure
    twp_value
    imodintro
    ipureintro
    exact Val.ext (by rw [decide_eq_true hagree])
  | succ r IH =>
    have hj : j < n := by omega
    have hlt : ¬(n : ℤ) ≤ (j : ℤ) := by omega
    have hn' : n = (j + 1) + r := by omega
    iterate 3 twp_pure
    simp only [hlt, _root_.decide_false]
    twp_pure
    twp_bind pl(&Occil.General.applyMaps &(mapsVal maps).fst #int (j : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_applyMaps E maps ⟨j, hj⟩
    iintro %v %hv
    subst v
    twp_pures
    simp only [stateVal, state_beq]
    by_cases he : applyMaps maps ⟨j, hj⟩ = first
    · have hdec : decide (AgreeFrom maps first j) = decide (AgreeFrom maps first (j + 1)) :=
        by simp only [agreeFrom_step maps first j hj, he, _root_.true_and]
      simp only [he, _root_.decide_true, hdec]
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&(allStates maps first) #int ((j + 1 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH (j + 1) hn'
    · have hnot : ¬AgreeFrom maps first j := fun h => he (h _ le_rfl)
      simp only [he, hnot, _root_.decide_false]
      twp_pures
      twp_value
      imodintro
      itrivial

/-- Repeated map callbacks expose the chronological iid-list law. -/
theorem repeatMaps_distSpec (E : CoPset) {n : ℕ} (ρ : MeasureTheory.Measure (Map n))
    [MeasureTheory.IsProbabilityMeasure ρ] (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) ρ mapVal) (h : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.repeatSample &sample.fst #int (h : ℤ))
      (IIDList.law ρ h) mapsVal := by
  have hspec := (SampleWithReplacement.repeatSample_distSpec E ρ mapVal sample hsample h).map
    List.ofFn (measurable_of_countable _) mapsVal (fun _ => rfl)
  simpa only [IIDList.vector_map] using hspec

end specification

end

end SampLib.CouplingFromPast
