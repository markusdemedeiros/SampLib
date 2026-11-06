import SampLib.Discrete.Laws.GaltonWatson
import SampLib.Discrete.PoissonRational
import Samplers.Discrete.Counts

/-! # Borel sampling by exploration of a Poisson Galton–Watson tree

The target is the independently constructed total-progeny law. Its branching
identity preserves output credit; the pending population pays for termination.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.Borel

noncomputable section

section mathematics

open MeasureTheory

/-- The normalized total-progeny law in the subcritical regime. -/
def law (r : ℝ≥0) (_hr : r < 1) : Measure ℕ := GaltonWatson.law r

instance (r : ℝ≥0) (hr : r < 1) : IsProbabilityMeasure (law r hr) where
  measure_univ := GaltonWatson.law_mass r hr

def amplification (r : ℝ≥0) (hr : r < 1) : ℝ≥0 :=
  ⟨2 - r, by
    have h : (r : ℝ) < 1 := by exact_mod_cast hr
    linarith⟩

theorem amplification_gt_one (r : ℝ≥0) (hr : r < 1) : 1 < amplification r hr := by
  have h : (r : ℝ) < 1 := by exact_mod_cast hr
  change (1 : ℝ) < 2 - r
  linarith

private theorem amplification_add_rate (r : ℝ≥0) (hr : r < 1) :
    (amplification r hr : ℝ≥0∞) + r = 2 := by
  have h : amplification r hr + r = 2 := by
    apply NNReal.coe_injective
    change (2 - (r : ℝ)) + r = 2
    ring
  exact_mod_cast h

def budget (r : ℝ≥0) (pending population : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  GaltonWatson.credit r pending population F + ε * pending

def kernel (r : ℝ≥0) (hr : r < 1) (pending population : ℕ)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  budget r (pending + k) (population + 1) F ε + amplification r hr * ε

/-- Branching preserves the continuation, and the offspring mean exactly pays
for the amplified termination credit and the next pending population. -/
theorem expectation (r : ℝ≥0) (hr : r < 1) (pending population : ℕ)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, kernel r hr pending population F ε k ∂ProbabilityTheory.poissonMeasure r) =
      budget r (pending + 1) population F ε + ε := by
  simp only [kernel, budget, Nat.cast_add, Nat.cast_one, mul_add]
  rw [lintegral_add_left (measurable_of_countable _) _,
    lintegral_add_left (measurable_of_countable _) _,
    lintegral_add_left (measurable_of_countable _) _,
    lintegral_const_mul (f := fun k : ℕ => (k : ℝ≥0∞)) ε
      (measurable_of_countable _), GaltonWatson.poisson_mean,
    ← GaltonWatson.credit_recurrence]
  simp only [lintegral_const, measure_univ, mul_one]
  have h := amplification_add_rate r hr
  calc
    _ = GaltonWatson.credit r (pending + 1) population F +
        ε * pending + ε * ((amplification r hr : ℝ≥0∞) + r) := by ring
    _ = _ := by rw [h]; ring

theorem rate_lt_one (x y : ℕ) (hxy : x < y) : PoissonRational.rate x y < 1 := by
  unfold PoissonRational.rate
  exact (div_lt_one (by exact_mod_cast (Nat.zero_lt_of_lt hxy))).mpr (by exact_mod_cast hxy)

private theorem valid_test (x y : ℕ) (hxy : x < y) :
    Bool.or false (decide ((y : ℤ) ≤ x)) = false := by
  simp [show ¬(y : ℤ) ≤ x by omega]

private theorem termination_credit (δ : ℝ≥0∞) (hδ : 0 < δ) (pending : ℕ) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ δ = ε * pending + ε := by
  refine ⟨δ / (pending + 1), ENNReal.div_pos hδ.ne' (by finiteness), ?_⟩
  have h : δ / (pending + 1) * (pending + 1) = δ :=
    ENNReal.div_mul_cancel (by positivity) (by finiteness)
  rw [mul_add, mul_one] at h
  exact h.symm

end mathematics

private def loop {rT : Type _} (x y : ℕ) : Exp rT :=
  .fix (.lam (.lam (.cond (pl% {Exp.bvar 1} = #0) (.bvar 0)
    (.app (.lam (pl% {Exp.bvar 3} ({Exp.bvar 2} - #1 + {Exp.bvar 0})
      ({Exp.bvar 1} + #1)))
      (pl% &Occil.poissonRational #int (x : ℤ) #int (y : ℤ))))))

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop_amplification (E : CoPset) (x y : ℕ) (hxy : x < y)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ⊢ ↯ ε -∗ ∀ pending : ℕ, ∀ population : ℕ,
      ↯ (budget (PoissonRational.rate x y) pending population F ε) -∗
      tglWp E pl(&(loop x y) #int (pending : ℤ) #int (population : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hterm
  iapply (ErrorCredit.Induction.simple hε
    (amplification_gt_one _ (rate_lt_one x y hxy))) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %pending %population Hcredit
  iterate 4 twp_pure
  rw [int_beq]
  cases pending with
  | zero =>
    rw [Nat.cast_zero, beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iexists population
    isimp only [budget, GaltonWatson.credit_zero, Nat.cast_zero, mul_zero, add_zero]
      at Hcredit
    iframe Hcredit
    itrivial
  | succ pending =>
    rw [beq_eq_false_iff_ne.mpr (by omega)]
    twp_pure
    simp only [PoissonRational.poissonRational_openRec]
    twp_bind pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
    icombine Hcredit Hterm as Hcredit
    isimp only [← expectation (PoissonRational.rate x y) (rate_lt_one x y hxy)
      pending population F ε] at Hcredit
    iapply ((PoissonRational.poissonRational_distSpec E x y (Nat.zero_lt_of_lt hxy)).wp
      (kernel _ (rate_lt_one x y hxy) pending population F ε)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %k Hcredit
    iterate 4 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add, ← Nat.cast_add_one]
    isimp only [kernel] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [loop] at IH
    isimp only [Exp.ofVal, PoissonRational.poissonRational_openRec]
    iapply IH $$ Hterm %(pending + k) %(population + 1) Hcredit

private theorem twp_loop (E : CoPset) (x y : ℕ) (hxy : x < y)
    (pending population : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (GaltonWatson.credit (PoissonRational.rate x y) pending population F) -∗
      tglWp E pl(&(loop x y) #int (pending : ℤ) #int (population : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨ε, hε, hbudget⟩ := termination_credit δ hδ pending
  isimp only [hbudget] at Hterm
  ihave ⟨Hextra, Hterm⟩ := ErrorCredit.split $$ Hterm
  icombine Hcredit Hextra as Hcredit
  iapply (twp_loop_amplification E x y hxy F ε hε) $$ Hterm %pending %population
  isimp only [budget]
  iexact Hcredit

theorem twp_borel (E : CoPset) (x y : ℕ) (hxy : x < y) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ n, F n ∂law (PoissonRational.rate x y) (rate_lt_one x y hxy)) -∗
      tglWp E pl(&Occil.DiscreteExtra.borel #int (x : ℤ) #int (y : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  twp_pures
  rw [valid_test x y hxy]
  iterate 2 twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec]
  have h := twp_loop (rT := rT) (GF := GF) E x y hxy 1 0 F
  simp only [GaltonWatson.initial_credit, loop] at h
  isimp only [law] at Hcredit
  iapply h $$ Hcredit

theorem borel_distSpec (E : CoPset) (x y : ℕ) (hxy : x < y) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.borel #int (x : ℤ) #int (y : ℤ))
      (law (PoissonRational.rate x y) (rate_lt_one x y hxy)) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := wand_entails (twp_borel E x y hxy F)

end specification

end

end SampLib.Borel
