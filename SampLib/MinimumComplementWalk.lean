import SampLib.Distributions.MinimumComplementBudget
import SampLib.Samplers.FairCoin
import SampLib.WeightedAmplification

/-! # The minimum-complement factory's first-passage walk

Finite barriers fund the critical fair walk without requiring a finite expected
running time. Its harmonic continuation credit survives every recursive step.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.MinimumComplement

noncomputable section

def walk {rT : Type _} : Exp rT :=
  let state := Exp.bvar 1
  let steps := Exp.bvar 0
  let next := Exp.binop .plus steps pl(#1)
  let recurse (direction : BinOp) :=
    Exp.app (.app (.bvar 2) (.binop direction state pl(#1))) next
  .fix (.lam (.lam (.cond (.binop .lt state pl(#0))
    (.binop .div next pl(#2))
    (.cond (.app Occil.fairCoin pl(#())) (recurse .plus) (recurse .minus)))))

theorem walk_lc {rT : Type _} : (walk : Exp rT).IsLocallyClosed := by
  unfold walk
  is_lc

theorem walk_fv {rT : Type _} : (walk : Exp rT).fv = ∅ := by
  simp [walk, Exp.fv, FairCoin.fairCoin_fv]

@[simp] theorem walk_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e walk = walk := (Exp.open_lc k e _ walk_lc).symm

@[simp] theorem walk_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (walk : Exp rT) = walk :=
  Exp.closeRec_fresh x _ k (by simp [walk_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def State (B : ℕ) := {q : ℕ × ℕ // q.1 ≤ B ∧ (q.1 + q.2) % 2 = 1}

private def baseCredit (t : unitInterval) (B k s : ℕ) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (Walk.bias t k s) F + Barrier.escape B k

private theorem walk_budget (t : unitInterval) (B k s : ℕ)
    (hk : 0 < k) (hkB : k < B) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ b, baseCredit t B (if b then k + 1 else k - 1) (s + 1) F +
      (Barrier.amplifier B : ℝ≥0∞) * ε *
        Barrier.potential B (if b then k + 1 else k - 1)
      ∂RealCoin.law VonNeumann.fairBias) ≤
      baseCredit t B k s F + ε * Barrier.potential B k := by
  simpa only [baseCredit, next, add_assoc] using expectation t B k s hk hkB F ε

private theorem twp_weighted (E : CoPset) (t : unitInterval) (B : ℕ) (hB : 0 < B)
    (F : Bool → ℝ≥0∞) (Φ : Val rT → IProp GF)
    (hreturn : ∀ s : ℕ, s % 2 = 1 →
      ⊢ ↯ (RealCoin.credit (Walk.bias t 0 s) F) -∗
        tglWp E pl(#int (((s : ℤ) + 1) / 2)) Φ)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ∀ q : State B, ↯ (ε * Barrier.potential B q.val.1) -∗
      ↯ (baseCredit t B q.val.1 q.val.2 F) -∗
        tglWp E pl(&walk #int ((q.val.1 : ℤ) - 1) #int (q.val.2 : ℤ)) Φ := by
  iapply ErrorCredit.Induction.weighted
    (fun q : State B => Barrier.potential B q.val.1)
    (fun q => Barrier.one_le_potential B q.val.1) _ ε hε
    (Barrier.amplifier B) (Barrier.one_lt_amplifier B hB) $$ []
  iintro !> %ε %hε #IH %q Hterm Hcredit
  isimp only [walk] at IH
  by_cases htop : q.val.1 = B
  · have hbig : 1 ≤ baseCredit t B q.val.1 q.val.2 F := by
      rw [baseCredit, htop, Barrier.escape_at_barrier B hB]
      exact le_add_left le_rfl
    iexfalso
    iapply ErrorCredit.contradict hbig $$ Hcredit
  by_cases hzero : q.val.1 = 0
  · isimp only [baseCredit, hzero, Barrier.escape, Nat.cast_zero, zero_div,
      ENNReal.coe_zero, add_zero] at Hcredit
    simp only [walk, hzero]
    twp_pures
    have hs : q.val.2 % 2 = 1 := by simpa [hzero] using q.property.2
    iapply hreturn q.val.2 hs $$ Hcredit
  have hk : 0 < q.val.1 := by omega
  have hkB : q.val.1 < B := by have := q.property.1; omega
  let down : State B := ⟨(q.val.1 - 1, q.val.2 + 1), by
    constructor
    · omega
    · have := q.property.2; omega⟩
  let up : State B := ⟨(q.val.1 + 1, q.val.2 + 1), by
    constructor
    · omega
    · have := q.property.2; omega⟩
  simp only [walk]
  iterate 3 twp_pure
  have hguard : decide ((q.val.1 : ℤ) - 1 < 0) = false := by simp; omega
  twp_pure
  rw [hguard]
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (walk_budget t B q.val.1 q.val.2 hk hkB F ε) $$ Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp _ (measurable_of_countable _) _) $$ Hsample
  iintro %b Htotal
  cases b
  · isimp only [Bool.false_eq_true, ite_false] at Htotal
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Htotal
    iterate 3 twp_pure
    have hstate : (q.val.1 : ℤ) - 1 - 1 = ((q.val.1 - 1 : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q.val.1), Nat.cast_one]
    rw [hstate, ← Nat.cast_add_one]
    simp only [FairCoin.fairCoin_openRec, Exp.ofVal]
    iapply IH $$ %down Hterm Hcredit
  · isimp only [ite_true] at Htotal
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Htotal
    iterate 3 twp_pure
    have hstate : (q.val.1 : ℤ) - 1 + 1 = ((q.val.1 + 1 : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_add_one]
      omega
    rw [hstate, ← Nat.cast_add_one]
    simp only [FairCoin.fairCoin_openRec, Exp.ofVal]
    iapply IH $$ %up Hterm Hcredit

/-- Any continuation funded by the absorbing harmonic credit can follow the walk. -/
theorem twp_walk (E : CoPset) (t : unitInterval) (F : Bool → ℝ≥0∞)
    (Φ : Val rT → IProp GF)
    (hreturn : ∀ s : ℕ, s % 2 = 1 →
      ⊢ ↯ (RealCoin.credit (Walk.bias t 0 s) F) -∗
        tglWp E pl(#int (((s : ℤ) + 1) / 2)) Φ) :
    ⊢ ↯ (RealCoin.credit (Walk.bias t 1 0) F) -∗
      tglWp E pl(&walk #0 #0) Φ := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨δ₀, hδ₀, hδ₀δ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  obtain ⟨B, η, hB, hη, hbudget⟩ := initial_slack δ₀ (by exact_mod_cast hδ₀)
  have hbudgetE : (Barrier.escape B 1 : ℝ≥0∞) + η * Barrier.potential B 1 ≤ δ₀ := by
    exact_mod_cast hbudget
  have haux := hbudgetE.trans hδ₀δ.le
  ihave Hterm := ErrorCredit.weaken haux $$ Hterm
  ihave ⟨Hescape, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hescape as Hcredit
  let start : State B := ⟨(1, 0), by constructor <;> omega⟩
  have h := twp_weighted (rT := rT) E t B (by omega) F Φ hreturn η
    (ENNReal.coe_pos.mpr hη)
  simp only [baseCredit] at h
  ieval (
    change _ ⊢ tglWp E
      pl(&walk #int ((start.val.1 : ℤ) - 1) #int (start.val.2 : ℤ)) Φ)
  iapply h $$ %start Hterm Hcredit

/-- Natural first-passage indices expose the exact downstream binomial credit. -/
theorem twp_index (E : CoPset) (p : unitInterval) (F : Bool → ℝ≥0∞)
    (Φ : Val rT → IProp GF)
    (hreturn : ∀ m : ℕ, 0 < m →
      ⊢ ↯ (RealCoin.credit (conditionalBias p m) F) -∗
        tglWp E pl(#int (m : ℤ)) Φ) :
    ⊢ ↯ (RealCoin.credit (Walk.bias (Walk.parameter p) 1 0) F) -∗
      tglWp E pl(&walk #0 #0) Φ := by
  iapply twp_walk E (Walk.parameter p) F Φ
  intro s hs
  let m := (s + 1) / 2
  have hm : 0 < m := by dsimp [m]; omega
  have hclock : s = 2 * m - 1 := by dsimp [m]; omega
  have hbias : Walk.bias (Walk.parameter p) 0 s = conditionalBias p m := by
    apply Subtype.ext
    change Walk.coefficient (Walk.parameter p) 0 s = _
    rw [hclock, Walk.absorbed p m hm]
    rfl
  have hcast : ((s : ℤ) + 1) / 2 = (m : ℤ) := by
    simp only [m, Int.natCast_ediv, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  simpa only [hbias, hcast] using hreturn m hm

end specification

end

end SampLib.MinimumComplement
