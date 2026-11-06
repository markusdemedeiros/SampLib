import SampLib.Distributions.AlternatingSeries
import SampLib.FactoryFractions

/-! # Rational accumulator invariants for the alternating-series engine -/

open ProbLang
open scoped ENNReal

namespace SampLib.AlternatingSeries

open FactoryFractions

noncomputable section

def stepTerm (c : Fraction) (b : Bool) : Fraction := if b then c else .ofRat 0

def stepLower (n : ℕ) (lo hi c : Fraction) (b : Bool) : Fraction :=
  if (n + 1) % 2 = 1 then .ofRat (hi.value - (stepTerm c b).value) else lo

def stepUpper (n : ℕ) (lo hi c : Fraction) (b : Bool) : Fraction :=
  if (n + 1) % 2 = 0 then .ofRat (lo.value + (stepTerm c b).value) else hi

/-- A successful callback advances one alternating bound; a failure collapses both. -/
theorem step_values (a : Parameters) (n : ℕ) (lo hi c : Fraction)
    (hlo : (lo.value : ℝ) = lower a n) (hhi : (hi.value : ℝ) = upper a n)
    (hc : (c.value : ℝ) = value a (n + 1)) (b : Bool) :
    ((stepLower n lo hi c b).value : ℝ) =
        (if b then lower a (n + 1) else partialSum a n) ∧
      ((stepUpper n lo hi c b).value : ℝ) =
        (if b then upper a (n + 1) else partialSum a n) := by
  obtain hn | hn := Nat.mod_two_eq_zero_or_one n
  · have hn1 : (n + 1) % 2 = 1 := by omega
    cases b <;>
      simp [stepLower, stepUpper, stepTerm, hhi, hc, lower, upper, partialSum, sub_eq_add_neg,
        AlternatingEnclosure.lower, AlternatingEnclosure.upper,
        AlternatingEnclosure.partial_succ, AlternatingEnclosure.sign, hn, hn1]
  · have hn1 : (n + 1) % 2 = 0 := by omega
    cases b <;>
      simp [stepLower, stepUpper, stepTerm, hlo, hc, lower, upper, partialSum,
        AlternatingEnclosure.lower, AlternatingEnclosure.upper,
        AlternatingEnclosure.partial_succ, AlternatingEnclosure.sign, hn, hn1]

/-- The deterministic accumulator state along the only continuing callback branch. -/
def state (raw : ℕ → Fraction) : ℕ → Fraction × Fraction
  | 0 => (.ofRat 0, raw 0)
  | n + 1 =>
      let previous := state raw n
      (stepLower n previous.1 previous.2 (raw (n + 1)) true,
        stepUpper n previous.1 previous.2 (raw (n + 1)) true)

theorem state_values (a : Parameters) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (n : ℕ) :
    (((state raw n).1).value : ℝ) = lower a n ∧
      (((state raw n).2).value : ℝ) = upper a n := by
  induction n with
  | zero =>
    simp [state, lower, upper, AlternatingEnclosure.lower_zero,
      AlternatingEnclosure.upper_zero, hraw, value]
  | succ n ih =>
    have hc : ((raw (n + 1)).value : ℝ) = value a (n + 1) := by rw [hraw]; rfl
    simpa only [state, ite_true] using
      step_values a n _ _ _ ih.1 ih.2 hc true

theorem branch_lower_credit (a : Parameters) (p : unitInterval) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (b : Bool)
    (h : DyadicPosterior.resolves q
      ((stepLower n (state raw n).1 (state raw n).2 (raw (n + 1)) b).value : ℝ) true) :
    F true ≤ DyadicPosterior.credit q (branchCredit a p N n F b) := by
  have hc : ((raw (n + 1)).value : ℝ) = value a (n + 1) := by rw [hraw]; rfl
  have hv := (step_values a n _ _ _ (state_values a raw hraw n).1
    (state_values a raw hraw n).2 hc b).1
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hv
    rw [hv] at h
    exact failed_lower_credit a N n q F h
  · simp only [ite_true] at hv
    rw [hv] at h
    exact lower_credit a p N (n + 1) q F h

theorem branch_upper_credit (a : Parameters) (p : unitInterval) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (N n : ℕ) (q : List Bool)
    (F : Bool → ℝ≥0∞) (b : Bool)
    (h : DyadicPosterior.resolves q
      ((stepUpper n (state raw n).1 (state raw n).2 (raw (n + 1)) b).value : ℝ) false) :
    F false ≤ DyadicPosterior.credit q (branchCredit a p N n F b) := by
  have hc : ((raw (n + 1)).value : ℝ) = value a (n + 1) := by rw [hraw]; rfl
  have hv := (step_values a n _ _ _ (state_values a raw hraw n).1
    (state_values a raw hraw n).2 hc b).2
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hv
    rw [hv] at h
    exact failed_upper_credit a N n q F h
  · simp only [ite_true] at hv
    rw [hv] at h
    exact upper_credit a p N (n + 1) q F h

/-- Once the input coin fails, the equal bounds cannot leave an unresolved comparison. -/
theorem retry_resolves (a : Parameters) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (n : ℕ) (q : List Bool) (b : Bool)
    (hlo : DyadicPosterior.resolves q
      ((stepLower n (state raw n).1 (state raw n).2 (raw (n + 1)) b).value : ℝ) false)
    (hhi : DyadicPosterior.resolves q
      ((stepUpper n (state raw n).1 (state raw n).2 (raw (n + 1)) b).value : ℝ) true) :
    b = true ∧ DyadicPosterior.resolves q (lower a (n + 1)) false ∧
      DyadicPosterior.resolves q (upper a (n + 1)) true := by
  have hc : ((raw (n + 1)).value : ℝ) = value a (n + 1) := by rw [hraw]; rfl
  have hv := step_values a n _ _ _ (state_values a raw hraw n).1
    (state_values a raw hraw n).2 hc b
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hv
    rw [hv.1] at hlo
    rw [hv.2] at hhi
    exact False.elim (resolved_conflict q _ hlo hhi)
  · simp only [ite_true] at hv
    rw [hv.1] at hlo
    rw [hv.2] at hhi
    exact ⟨rfl, hlo, hhi⟩

end

end SampLib.AlternatingSeries
