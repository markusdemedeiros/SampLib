import SampLib.Discrete.Laws.PoissonOne
import SampLib.Common.Laws.PoissonTree
import SampLib.Core.SupportedSpec
import SampLib.Uniform.RndInt
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Duchon–Duvignau's unit-rate Poisson sampler

Parity-subset counting identifies the absorption law. Program execution follows
one uniform rank; the gap to the boundary supplies the termination potential.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PoissonOne

noncomputable section

open PoissonTree

def Valid (s : State) : Prop :=
  2 ≤ s.size ∧ s.boundary ≤ s.size ∧ s.size - s.boundary ≤ s.count

theorem valid_up (s : State) (hs : Valid s) : Valid s.up := by
  rcases hs with ⟨ha, hb, hr⟩
  dsimp only [Valid, State.up]
  omega

theorem valid_down (s : State) (hs : Valid s) : Valid s.down := by
  rcases hs with ⟨ha, hb, hr⟩
  dsimp only [Valid, State.down]
  omega

theorem down_count_cast (s : State) (hs : Valid s) (j : ℕ)
    (hj : j < s.size) (hb : s.boundary ≤ j) :
    (s.count : ℤ) - 1 = (s.down.count : ℤ) := by
  rcases hs with ⟨ha, hbound, hr⟩
  dsimp only [State.down]
  omega

private theorem stop_test (a b j : ℕ) (hb : b ≤ a) :
    Bool.and (decide ((j : ℤ) < a)) (decide ((j : ℤ) < b)) = decide (j < b) := by
  by_cases h : j < b
  · have hja : (j : ℤ) < a := by omega
    have hjb : (j : ℤ) < b := by omega
    simp [h, hja, hjb]
  · have hjb : ¬(j : ℤ) < b := by omega
    simp [h, hjb]

theorem poissonOne_lc {rT : Type _} : (Occil.poissonOne : Exp rT).IsLocallyClosed := by
  is_lc

theorem poissonOne_fv {rT : Type _} : (Occil.poissonOne : Exp rT).fv = ∅ := by
  simp [Occil.poissonOne, RndInt.rndInt_fv, Exp.fv]

@[simp] theorem poissonOne_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.poissonOne = Occil.poissonOne :=
  (Exp.open_lc k e _ poissonOne_lc).symm

@[simp] theorem poissonOne_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.poissonOne : Exp rT) = Occil.poissonOne :=
  Exp.closeRec_fresh x _ k (by simp [poissonOne_fv])

private def loop {rT : Type _} : Exp rT := pl%
  rec draw ret a b :=
    let j := &Occil.rndInt a;
    if (j < a) && (j < b) then ret else
    if j = a then draw (ret + #1) (a + #1) b
    else draw (ret - #1) (a + #1) (a + #1)

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop_amplification (E : CoPset) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ↯ ε -∗ ∀ s : State, ⌜Valid s⌝ -∗ ↯ (budget s F ε) -∗
      tglWp E pl(&loop #int (s.count : ℤ) #int (s.size : ℤ) #int (s.boundary : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hterm
  iapply (ErrorCredit.Induction.simple (k := 2) hε one_lt_two) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %s %hs Hcredit
  iterate 4 twp_pure
  simp only [RndInt.rndInt_openRec, RndInt.rndInt_closeRec]
  twp_bind pl(&Occil.rndInt #int (s.size : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken (expectation s hs.2.1 F ε (Or.inr hs.1)) $$ Hcredit
  iapply ((RndInt.rndInt_distSpec E s.size).wp_supported (fun j => j ≤ s.size)
    (Set.to_countable _).measurableSet (rank_support s.size) (rankCredit s F ε)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %j %hj Hcredit
  twp_pures
  rw [stop_test s.size s.boundary j hs.2.1]
  by_cases hstop : j < s.boundary
  · rw [decide_eq_true hstop]
    twp_pures
    twp_value
    imodintro
    iexists s.count
    isimp only [rankCredit, rankKernel, ite_eq_left hstop] at Hcredit
    iframe Hcredit
    itrivial
  · rw [decide_eq_false hstop]
    twp_pures
    rw [int_beq]
    by_cases hmax : j = s.size
    · subst j
      rw [beq_self_eq_true]
      iterate 3 twp_pure
      isimp only [Exp.ofVal, RndInt.rndInt_openRec, RndInt.rndInt_closeRec,
        ← Nat.cast_add_one]
      isimp only [rankCredit, rankKernel, ite_eq_right hstop, ite_true] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      isimp [loop, Exp.close, Exp.closeRec] at IH
      isimp [Exp.close, Exp.closeRec]
      ihave Hnext := IH $$ Hterm %s.up %(valid_up s hs) Hcredit
      isimp only [State.up, Nat.cast_add, Nat.cast_one] at Hnext
      iexact Hnext
    · rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hmax)]
      iterate 4 twp_pure
      rw [down_count_cast s hs j (lt_of_le_of_ne hj hmax) (Nat.le_of_not_gt hstop)]
      isimp only [Exp.ofVal, RndInt.rndInt_openRec, RndInt.rndInt_closeRec,
        ← Nat.cast_add_one]
      isimp only [rankCredit, rankKernel, ite_eq_right hstop, ite_eq_right hmax] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      isimp [loop, Exp.close, Exp.closeRec] at IH
      isimp [Exp.close, Exp.closeRec]
      ihave Hnext := IH $$ Hterm %s.down %(valid_down s hs) Hcredit
      isimp only [State.down, Nat.cast_add, Nat.cast_one] at Hnext
      isimp only [State.down]
      iexact Hnext

private theorem twp_loop (E : CoPset) (s : State) (hs : Valid s) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit s F) -∗
      tglWp E pl(&loop #int (s.count : ℤ) #int (s.size : ℤ) #int (s.boundary : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨ε, hε, hbudget⟩ := termination_credit δ hδ (s.size - s.boundary)
  isimp only [hbudget] at Hterm
  ihave ⟨Hextra, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hextra as Hcredit
  iapply (twp_loop_amplification E F ε hε) $$ Hterm %s %hs
  isimp only [budget]
  iexact Hcredit

private theorem twp_entry (E : CoPset) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit ⟨1, 1, 0⟩ F) -∗ tglWp E pl(&loop #1 #1 #0)
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  have hexpect := expectation (⟨1, 1, 0⟩ : State) (by decide) F 0 (Or.inl rfl)
  simp only [budget, zero_mul, add_zero] at hexpect
  iintro Hcredit
  iterate 4 twp_pure
  simp only [RndInt.rndInt_openRec, RndInt.rndInt_closeRec]
  twp_bind pl(&Occil.rndInt #1)
  ihave Hcredit := ErrorCredit.weaken hexpect $$ Hcredit
  iapply ((RndInt.rndInt_distSpec E 1).wp_supported (fun j => j ≤ 1)
    (Set.to_countable _).measurableSet (rank_support 1) (rankCredit ⟨1, 1, 0⟩ F 0)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %j %hj Hcredit
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · iterate 10 twp_pure
    isimp only [Exp.ofVal, RndInt.rndInt_openRec, RndInt.rndInt_closeRec]
    isimp [rankCredit, rankKernel, budget, State.up, State.down] at Hcredit
    have h := twp_loop (rT := rT) (GF := GF) E ⟨0, 2, 2⟩ (by norm_num [Valid]) F
    simp [loop, Exp.close, Exp.closeRec] at h
    iapply h $$ Hcredit
  · iterate 9 twp_pure
    isimp only [Exp.ofVal, RndInt.rndInt_openRec, RndInt.rndInt_closeRec]
    isimp [rankCredit, rankKernel, budget, State.up, State.down] at Hcredit
    have h := twp_loop (rT := rT) (GF := GF) E ⟨2, 2, 0⟩ (by norm_num [Valid]) F
    simp [loop, Exp.close, Exp.closeRec] at h
    iapply h $$ Hcredit

/-- The integer-only sampler has the standard unit-rate Poisson law. -/
theorem twp_poissonOne (E : CoPset) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂ProbabilityTheory.poissonMeasure 1) -∗
      tglWp E pl(&Occil.poissonOne #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  have h := twp_entry (rT := rT) (GF := GF) E F
  simp [loop, Exp.close, Exp.closeRec] at h
  iintro Hcredit
  isimp only [← initial_credit F] at Hcredit
  iterate 2 twp_pure
  simp only [RndInt.rndInt_openRec, RndInt.rndInt_closeRec]
  iapply h $$ Hcredit

theorem poissonOne_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.poissonOne #())
      (ProbabilityTheory.poissonMeasure 1) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_poissonOne E F)

end specification

end

end SampLib.PoissonOne
