module

public import SampLib.Constants.Laws.CriticalBranching
public import SampLib.Constants.Laws.RealContinuedFraction

@[expose] public section

/-! # Finite trees for the fair two-call coin recursion

On the stopping branch, sample the coefficient coin. Otherwise sample the tail;
its success returns false, and its failure restarts the current position. The two
partial masses record actual returns before the chosen recursion depth. Their
missing mass is bounded by critical fair binary branching.
-/

namespace SampLib.CriticalCoin

noncomputable section

/-- A coefficient coin and its positive mathematical bias. -/
structure Coefficient where
  bias : unitInterval
  positive : 0 < (bias : ℝ)
  last : Bool

/-- Exactly the positions before or at the first final coefficient. -/
def Reachable (a : ℕ → Coefficient) (start i : ℕ) : Prop :=
  start ≤ i ∧ ∀ j, start ≤ j → j < i → (a j).last = false

theorem reachable_self (a : ℕ → Coefficient) (start : ℕ) : Reachable a start start :=
  ⟨le_rfl, by intro j hj hj'; omega⟩

theorem reachable_next {a : ℕ → Coefficient} {start i : ℕ}
    (hi : Reachable a start i) (hlast : (a i).last = false) : Reachable a start (i + 1) := by
  refine ⟨hi.1.trans (Nat.le_succ _), ?_⟩
  intro j hj hji
  by_cases hji' : j < i
  · exact hi.2 j hj hji'
  · have : j = i := by omega
    simpa [this] using hlast

def coefficients (a : ℕ → Coefficient) (i : ℕ) :
    RealContinuedFraction.Coefficient where
  numerator := (a i).bias
  denominator := 1
  positive := (a i).positive
  lower := le_rfl
  bounded := (a i).bias.2.2
  last := (a i).last

/-- The unique infinite fraction `b_i/(1+b_(i+1)/(1+...))`. -/
def bias (a : ℕ → Coefficient) (i : ℕ) : unitInterval :=
  RealContinuedFraction.value (coefficients a) i

theorem bias_pos (a : ℕ → Coefficient) (i : ℕ) : 0 < (bias a i : ℝ) :=
  RealContinuedFraction.value_pos (coefficients a) i

/-- The source's two-call mixture is the continued-fraction recurrence. -/
theorem bias_recurrence (a : ℕ → Coefficient) (i : ℕ)
    (hlast : (a i).last = false) :
    2 * (bias a i : ℝ) = (a i).bias +
      (1 - (bias a (i + 1) : ℝ)) * (bias a i : ℝ) := by
  have h := RealContinuedFraction.value_coe (coefficients a) i
  simp only [coefficients, hlast, Bool.false_eq_true, ite_false] at h
  change (bias a i : ℝ) = (a i).bias / (1 + (bias a (i + 1) : ℝ)) at h
  have hp : 0 < 1 + (bias a (i + 1) : ℝ) :=
    add_pos_of_pos_of_nonneg zero_lt_one (bias a (i + 1)).2.1
  rw [eq_div_iff hp.ne'] at h
  nlinarith

theorem bias_last (a : ℕ → Coefficient) (i : ℕ) (hlast : (a i).last = true) :
    bias a i = (a i).bias := by
  apply Subtype.ext
  have h := RealContinuedFraction.value_coe (coefficients a) i
  simpa only [bias, coefficients, hlast, ite_true, add_zero, div_one] using h

theorem bias_lt_one (a : ℕ → Coefficient) (i : ℕ)
    (hlast : (a i).last = false) : (bias a i : ℝ) < 1 := by
  have hrec := bias_recurrence a i hlast
  have hb := (a i).bias.2.2
  have hp := mul_pos (bias_pos a i) (bias_pos a (i + 1))
  nlinarith

/-- True and false return masses after finitely many unfoldings. -/
def masses (a : ℕ → Coefficient) : ℕ → ℕ → ℝ × ℝ
  | 0, _ => (0, 0)
  | n + 1, i =>
      if (a i).last then ((a i).bias, 1 - (a i).bias) else
      let tail := masses a n (i + 1)
      let again := masses a n i
      (((a i).bias + tail.2 * again.1) / 2,
        (1 - (a i).bias + tail.1 + tail.2 * again.2) / 2)

/-- No finite unfolding creates or loses mass except through unresolved calls. -/
theorem masses_valid (a : ℕ → Coefficient) (n i : ℕ) :
    0 ≤ (masses a n i).1 ∧ 0 ≤ (masses a n i).2 ∧
      (masses a n i).1 + (masses a n i).2 ≤ 1 := by
  induction n generalizing i with
  | zero => norm_num [masses]
  | succ n IH =>
    cases hlast : (a i).last
    ·
      have ht := IH (i + 1)
      have hr := IH i
      have hb := (a i).bias.property
      simp only [masses, hlast, Bool.false_eq_true, ite_false]
      refine ⟨div_nonneg (add_nonneg hb.1 (mul_nonneg ht.2.1 hr.1)) (by norm_num),
        div_nonneg (add_nonneg (add_nonneg (sub_nonneg.mpr hb.2) ht.1)
          (mul_nonneg ht.2.1 hr.2.1)) (by norm_num), ?_⟩
      nlinarith [mul_nonneg ht.2.1 (show 0 ≤ 1 - (masses a n i).1 -
        (masses a n i).2 by linarith)]
    ·
      simpa only [masses, hlast, ite_true] using
        And.intro (a i).bias.2.1
          (And.intro (sub_nonneg.mpr (a i).bias.2.2)
            (by linarith : (a i).bias + (1 - ((a i).bias : ℝ)) ≤ 1))

/-- Probability not yet returned within the chosen recursion depth. -/
def deficit (a : ℕ → Coefficient) (n i : ℕ) : ℝ :=
  1 - (masses a n i).1 - (masses a n i).2

/-- Unresolved tail calls persist; a returned false tail also exposes the retry deficit. -/
theorem deficit_succ (a : ℕ → Coefficient) (n i : ℕ) (hlast : (a i).last = false) :
    deficit a (n + 1) i =
      (deficit a n (i + 1) + (masses a n (i + 1)).2 * deficit a n i) / 2 := by
  simp only [deficit, masses, hlast, Bool.false_eq_true, ite_false]
  ring

/-- Unresolved calls are dominated by the critical binary-tree depth tail. -/
theorem missing_le (a : ℕ → Coefficient) (n i : ℕ) :
    1 - (masses a n i).1 - (masses a n i).2 ≤ CriticalBranching.survival n := by
  induction n generalizing i with
  | zero => norm_num [masses, CriticalBranching.survival]
  | succ n IH =>
    cases hlast : (a i).last
    · have ht := masses_valid a n (i + 1)
      have hr := masses_valid a n i
      have hs := CriticalBranching.survival_mem n
      have htail : deficit a n (i + 1) ≤ CriticalBranching.survival n := IH (i + 1)
      have hagain : deficit a n i ≤ CriticalBranching.survival n := IH i
      have hf : (masses a n (i + 1)).2 ≤ 1 - deficit a n (i + 1) := by
        dsimp only [deficit]
        linarith [ht.1]
      have hbudget : deficit a n (i + 1) +
          (masses a n (i + 1)).2 * deficit a n i ≤
            CriticalBranching.survival n +
              (1 - CriticalBranching.survival n) * CriticalBranching.survival n := by
        calc
          _ ≤ deficit a n (i + 1) +
              (1 - deficit a n (i + 1)) * CriticalBranching.survival n := by
            exact add_le_add le_rfl (mul_le_mul hf hagain
              (by dsimp only [deficit]; linarith [hr.2.2])
              (by dsimp only [deficit]; linarith [ht.1, ht.2.1]))
          _ ≤ _ := by
            nlinarith [mul_nonneg (sub_nonneg.mpr htail) (sub_nonneg.mpr hs.2)]
      change deficit a (n + 1) i ≤ _
      rw [deficit_succ a n i hlast]
      dsimp only [CriticalBranching.survival]
      nlinarith
    · simpa only [masses, hlast, ite_true, sub_sub_cancel, sub_self] using
        (CriticalBranching.survival_mem (n + 1)).1

/-- Each finite return mass is bounded by its canonical infinite-fraction mass. -/
theorem masses_le (a : ℕ → Coefficient) (n i : ℕ) :
    (masses a n i).1 ≤ (bias a i : ℝ) ∧
      (masses a n i).2 ≤ 1 - (bias a i : ℝ) := by
  induction n generalizing i with
  | zero => simpa only [masses] using ⟨(bias a i).2.1, sub_nonneg.mpr (bias a i).2.2⟩
  | succ n IH =>
    cases hlast : (a i).last
    ·
      have ht := IH (i + 1)
      have hr := IH i
      have hp := (bias a (i + 1)).property
      have hsame := masses_valid a n i
      have htrue := mul_le_mul ht.2 hr.1 hsame.1 (sub_nonneg.mpr hp.2)
      have hfalse := mul_le_mul ht.2 hr.2 hsame.2.1 (sub_nonneg.mpr hp.2)
      have hrec := bias_recurrence a i hlast
      simp only [masses, hlast, Bool.false_eq_true, ite_false]
      constructor <;> nlinarith
    ·
      simp only [masses, hlast, ite_true, bias_last a i hlast, le_refl, and_self]

/-- No positive mass remains in an infinitely deep call tree. -/
theorem missing_tendsto (a : ℕ → Coefficient) (i : ℕ) :
    Filter.Tendsto (fun n => 1 - (masses a n i).1 - (masses a n i).2)
      Filter.atTop (nhds 0) :=
  squeeze_zero (fun n => by linarith [(masses_valid a n i).2.2])
    (fun n => missing_le a n i) CriticalBranching.survival_tendsto

/-- Finite true-return masses converge to the unique fraction value. -/
theorem true_tendsto (a : ℕ → Coefficient) (i : ℕ) :
    Filter.Tendsto (fun n => (masses a n i).1) Filter.atTop (nhds (bias a i : ℝ)) := by
  have hz : Filter.Tendsto (fun n => (bias a i : ℝ) - (masses a n i).1)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (masses_le a n i).1)
      (fun n => by linarith [(masses_le a n i).2]) (missing_tendsto a i)
  have ht : Filter.Tendsto
      (fun n => (bias a i : ℝ) - ((bias a i : ℝ) - (masses a n i).1))
      Filter.atTop (nhds ((bias a i : ℝ) - 0)) := tendsto_const_nhds.sub hz
  simpa only [sub_sub_cancel, sub_zero] using ht

/-- Finite false-return masses converge to the complementary fraction mass. -/
theorem false_tendsto (a : ℕ → Coefficient) (i : ℕ) :
    Filter.Tendsto (fun n => (masses a n i).2) Filter.atTop
      (nhds (1 - (bias a i : ℝ))) := by
  have hz : Filter.Tendsto (fun n => 1 - (bias a i : ℝ) - (masses a n i).2)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => sub_nonneg.mpr (masses_le a n i).2)
      (fun n => by linarith [(masses_le a n i).1]) (missing_tendsto a i)
  have ht : Filter.Tendsto
      (fun n => (1 - (bias a i : ℝ)) - (1 - (bias a i : ℝ) - (masses a n i).2))
      Filter.atTop (nhds ((1 - (bias a i : ℝ)) - 0)) := tendsto_const_nhds.sub hz
  simpa only [sub_sub_cancel, sub_zero] using ht

end

end SampLib.CriticalCoin
