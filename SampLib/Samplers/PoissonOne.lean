import SampLib.Distributions.PoissonTree
import SampLib.SupportedSpec
import SampLib.Samplers.RndInt
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

section mathematics

open MeasureTheory Finset

def rankKernel (a b : ℕ) (T U D : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if j < b then T else if j = a then U else D

private theorem rank_mean (a b : ℕ) (hb : b ≤ a) (T U D : ℝ≥0∞) :
    (∫⁻ j, rankKernel a b T U D j ∂RndInt.law a) =
      ((b : ℝ≥0∞) * T + U + (a - b : ℕ) * D) / (a + 1) := by
  have hprefix : (∑ j ∈ range a, rankKernel a b T U D j) =
      (b : ℝ≥0∞) * T + (a - b : ℕ) * D := by
    have hreduce : (∑ j ∈ range a, rankKernel a b T U D j) =
        ∑ j ∈ range a, if j < b then T else D := by
      apply sum_congr rfl
      intro j hj
      simp [rankKernel, Nat.ne_of_lt (mem_range.mp hj)]
    rw [hreduce]
    conv_lhs => rw [← Nat.add_sub_of_le hb, sum_range_add]
    have hfirst : (∑ j ∈ range b, if j < b then T else D) = b * T := by
      calc
        _ = ∑ j ∈ range b, T := sum_congr rfl fun j hj => ite_eq_left (mem_range.mp hj)
        _ = _ := by simp [nsmul_eq_mul]
    rw [hfirst]
    simp [Nat.not_lt.mpr (Nat.le_add_right b _), nsmul_eq_mul]
  rw [RndInt.expectation, sum_range_succ, hprefix]
  simp only [rankKernel, Nat.not_lt.mpr hb, ite_false, ite_true,
    Nat.cast_add, Nat.cast_one]
  congr 1
  ring

def budget (s : State) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  credit s F + ε * (s.size - s.boundary : ℕ)

def rankCredit (s : State) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  rankKernel s.size s.boundary (F s.count)
    (budget s.up F ε + 2 * ε) (budget s.down F ε + 2 * ε)

/-- A live child receives its potential budget and twice the common termination
credit. Their expected total is at most the current potential budget. -/
theorem expectation (s : State) (hb : s.boundary ≤ s.size)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (ha : ε = 0 ∨ 2 ≤ s.size) :
    (∫⁻ j, rankCredit s F ε j ∂RndInt.law s.size) ≤ budget s F ε + ε := by
  have hdu : s.up.size - s.up.boundary = s.size - s.boundary + 1 := by
    dsimp only [State.up]
    omega
  have hdd : s.down.size - s.down.boundary = 0 := by simp [State.down]
  have hexact : (∫⁻ j, rankCredit s F ε j ∂RndInt.law s.size) =
      credit s F + ε * ((3 : ℝ≥0∞) * (s.size - s.boundary + 1 : ℕ) / (s.size + 1)) := by
    rw [rankCredit, rank_mean s.size s.boundary hb]
    rw [credit_recurrence s F]
    simp only [budget, hdu, hdd, Nat.cast_zero, mul_zero, add_zero,
      ENNReal.div_eq_inv_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [hexact]
  rcases ha with rfl | ha
  · simp [budget]
  · have hcoef : (3 : ℝ≥0∞) * (s.size - s.boundary + 1 : ℕ) / (s.size + 1) ≤
        (s.size - s.boundary + 1 : ℕ) := by
      apply (ENNReal.div_le_iff (by positivity) (by finiteness)).mpr
      have hthree : (3 : ℝ≥0∞) ≤ s.size + 1 := by
        exact_mod_cast (show 3 ≤ s.size + 1 by omega)
      simpa only [mul_comm] using
        mul_le_mul_left hthree (((s.size - s.boundary + 1 : ℕ) : ℝ≥0∞))
    calc
      _ ≤ credit s F + ε * (s.size - s.boundary + 1 : ℕ) :=
        add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul_left hcoef ε)
      _ = _ := by simp only [budget, Nat.cast_add, Nat.cast_one]; ring

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

private theorem termination_credit (δ : ℝ≥0∞) (hδ : 0 < δ) (d : ℕ) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ δ = ε * d + ε := by
  refine ⟨δ / (d + 1), ENNReal.div_pos hδ.ne' (by finiteness), ?_⟩
  have h : δ / (d + 1) * (d + 1) = δ :=
    ENNReal.div_mul_cancel (by positivity) (by finiteness)
  rw [mul_add, mul_one] at h
  exact h.symm

private theorem rank_support (a : ℕ) : ∀ᵐ j ∂RndInt.law a, j ≤ a := by
  simp only [RndInt.law, UniformInt.law, Measure.uniformOfFinset,
    ae_finsetSum_measure_iff]
  intro j hj
  apply Measure.ae_smul_measure _ ((range (a + 1)).card : ℝ≥0∞)⁻¹
  simpa using Nat.le_of_lt_succ (mem_range.mp hj)

private theorem stop_test (a b j : ℕ) (hb : b ≤ a) :
    Bool.and (decide ((j : ℤ) < a)) (decide ((j : ℤ) < b)) = decide (j < b) := by
  by_cases h : j < b
  · have hja : (j : ℤ) < a := by omega
    have hjb : (j : ℤ) < b := by omega
    simp [h, hja, hjb]
  · have hjb : ¬(j : ℤ) < b := by omega
    simp [h, hjb]

end mathematics

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
