import SampLib.Distributions.InverseUrn
import SampLib.Samplers.PolyaEggenberger

/-! # The rising-product mass function of the inverse urn -/

open MeasureTheory Measure
open scoped ENNReal

namespace SampLib.InverseUrn

noncomputable section

abbrev rising := PolyaEggenberger.rising

theorem rising_pos (a c : ℕ) (ha : 0 < a) (n : ℕ) : 0 < rising a c n := by
  induction n generalizing a with
  | zero => simp [rising, PolyaEggenberger.rising]
  | succ n ih =>
    exact Nat.mul_pos ha (ih (a + c) (by omega))

/-- The first draw is marked, or unmarked with one additional failure. -/
theorem law_succ (r a b c : ℕ) (ha : 0 < a) :
    law (r + 1) a b c ha =
      ((1 - UrnWaiting.continuation a b c 0) • law r (a + c) b c (by omega)) +
      (UrnWaiting.continuation a b c 0 • (law (r + 1) a (b + c) c ha).map Nat.succ) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_map hF (measurable_of_countable _)]
  exact expectation r a b c ha F

/-- Immediate stopping has no unmarked-draw contribution. -/
theorem mass_zero_recurrence (r a b c : ℕ) (ha : 0 < a) :
    law (r + 1) a b c ha {0} =
      (1 - UrnWaiting.continuation a b c 0) * law r (a + c) b c (by omega) {0} := by
  rw [law_succ]
  simp [Measure.map_apply (measurable_of_countable _), Set.preimage, smul_eq_mul]

/-- The unmarked first draw shifts the remaining failure count down by one. -/
theorem mass_succ_recurrence (r a b c n : ℕ) (ha : 0 < a) :
    law (r + 1) a b c ha {n + 1} =
      (1 - UrnWaiting.continuation a b c 0) * law r (a + c) b c (by omega) {n + 1} +
      UrnWaiting.continuation a b c 0 * law (r + 1) a (b + c) c ha {n} := by
  rw [law_succ]
  have hpre : Nat.succ ⁻¹' ({n + 1} : Set ℕ) = {n} := by ext; simp
  simp [Measure.map_apply (measurable_of_countable _), hpre, smul_eq_mul]

private theorem stop_probability (a b c : ℕ) (ha : 0 < a) :
    1 - UrnWaiting.continuation a b c 0 = (a : ℝ≥0∞) / (a + b) := by
  have hm := UrnWaiting.hazard_mem a b c 0 ha
  have hsum : ENNReal.ofReal (UrnWaiting.hazard a b c 0) +
      UrnWaiting.continuation a b c 0 = 1 := by
    rw [UrnWaiting.continuation, ← ENNReal.ofReal_add hm.1 (sub_nonneg.mpr hm.2)]
    simp
  have h := ENNReal.eq_sub_of_add_eq
    (by simp [UrnWaiting.continuation]) hsum
  rw [← h]
  have hd : (0 : ℝ) < a + b := by positivity
  simp [UrnWaiting.hazard, ENNReal.ofReal_div_of_pos hd,
    ENNReal.ofReal_add (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

private theorem continue_probability (a b c : ℕ) (ha : 0 < a) :
    UrnWaiting.continuation a b c 0 = (b : ℝ≥0∞) / (a + b) := by
  have hd : (0 : ℝ) < a + b := by positivity
  have heq : 1 - (a : ℝ) / (a + b) = b / (a + b) := by
    field_simp
    ring
  simp [UrnWaiting.continuation, UrnWaiting.hazard, heq,
    ENNReal.ofReal_div_of_pos hd,
    ENNReal.ofReal_add (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

/-- Zero failures means that every required marked draw occurs consecutively. -/
theorem mass_zero (r a b c : ℕ) (ha : 0 < a) :
    law r a b c ha {0} = (rising a c r : ℝ≥0∞) / rising (a + b) c r := by
  induction r generalizing a b with
  | zero => simp [law, rising, PolyaEggenberger.rising]
  | succ r ih =>
    rw [mass_zero_recurrence, stop_probability a b c ha, ih]
    rw [show (a + c) + b = (a + b) + c by omega]
    simp only [rising, PolyaEggenberger.rising, Nat.cast_mul]
    rw [← Nat.cast_add]
    rw [ENNReal.mul_div_mul_comm (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]


/-- The standard rising-product inverse-urn mass, with `r+1` marked draws. -/
def coefficient (r a b c n : ℕ) : ℝ :=
  (Nat.choose (r + n) n : ℝ) * rising a c (r + 1) * rising b c n /
    rising (a + b) c (r + 1 + n)

private theorem coefficient_nonneg (r a b c n : ℕ) : 0 ≤ coefficient r a b c n := by
  unfold coefficient
  positivity

/-- The nonnegative mass represented in the expectation semiring. -/
def positiveMass (r a b c n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (coefficient r a b c n)

private theorem marked_step (r a b c n : ℕ) :
    (a / (a + b) : ℝ) * coefficient r (a + c) b c n =
      (Nat.choose (r + n) n : ℝ) * rising a c (r + 2) * rising b c n /
        rising (a + b) c (r + 2 + n) := by
  unfold coefficient
  rw [show a + c + b = a + b + c by omega,
    show r + 2 + n = (r + 1 + n) + 1 by omega]
  rw [show r + 2 = (r + 1) + 1 by omega]
  simp only [rising, PolyaEggenberger.rising, Nat.cast_mul, Nat.cast_add,
    div_eq_mul_inv, mul_inv_rev]
  ring

private theorem unmarked_step (r a b c n : ℕ) :
    (b / (a + b) : ℝ) * coefficient r a (b + c) c n =
      (Nat.choose (r + n) n : ℝ) * rising a c (r + 1) * rising b c (n + 1) /
        rising (a + b) c (r + 2 + n) := by
  unfold coefficient
  rw [show a + (b + c) = a + b + c by omega,
    show r + 2 + n = (r + 1 + n) + 1 by omega]
  simp only [rising, PolyaEggenberger.rising, Nat.cast_mul, Nat.cast_add,
    div_eq_mul_inv, mul_inv_rev]
  ring

private theorem coefficient_one_step (a b c n : ℕ) :
    coefficient 0 a b c (n + 1) = (b / (a + b) : ℝ) * coefficient 0 a (b + c) c n := by
  rw [unmarked_step]
  simp [coefficient, Nat.add_comm, Nat.add_left_comm]

/-- Pascal's identity accounts for whether the first draw is marked or unmarked. -/
private theorem coefficient_recurrence (r a b c n : ℕ) :
    coefficient (r + 1) a b c (n + 1) =
      (a / (a + b) : ℝ) * coefficient r (a + c) b c (n + 1) +
      (b / (a + b) : ℝ) * coefficient (r + 1) a (b + c) c n := by
  rw [marked_step, unmarked_step]
  unfold coefficient
  have hchoose : Nat.choose (r + 1 + (n + 1)) (n + 1) =
      Nat.choose (r + (n + 1)) (n + 1) + Nat.choose (r + 1 + n) n := by
    simpa only [show r + 1 + (n + 1) = (r + n + 1) + 1 by omega,
      show r + (n + 1) = r + n + 1 by omega,
      show r + 1 + n = r + n + 1 by omega, Nat.succ_eq_add_one, Nat.add_comm] using
      Nat.choose_succ_succ (r + n + 1) n
  rw [hchoose]
  push_cast
  rw [show r + 1 + 1 = r + 2 by omega,
    show r + 2 + (n + 1) = r + 1 + 2 + n by omega]
  ring

private theorem positiveMass_zero (r a b c : ℕ) (ha : 0 < a) :
    positiveMass r a b c 0 = (rising a c (r + 1) : ℝ≥0∞) /
      rising (a + b) c (r + 1) := by
  simp only [positiveMass, coefficient, Nat.add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  rw [show rising b c 0 = 1 by rfl]
  simp only [Nat.cast_one, mul_one]
  have hd : (0 : ℝ) < PolyaEggenberger.rising (a + b) c (r + 1) := by
    exact_mod_cast rising_pos (a + b) c (by omega) (r + 1)
  rw [ENNReal.ofReal_div_of_pos hd]
  simp

private theorem positiveMass_one_step (a b c n : ℕ) (ha : 0 < a) :
    positiveMass 0 a b c (n + 1) =
      UrnWaiting.continuation a b c 0 * positiveMass 0 a (b + c) c n := by
  have hd : (0 : ℝ) < a + b := by positivity
  simp only [positiveMass]
  rw [coefficient_one_step, ENNReal.ofReal_mul (by positivity),
    continue_probability a b c ha, ENNReal.ofReal_div_of_pos hd]
  simp [ENNReal.ofReal_add (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

private theorem positiveMass_recurrence (r a b c n : ℕ) (ha : 0 < a) :
    positiveMass (r + 1) a b c (n + 1) =
      (1 - UrnWaiting.continuation a b c 0) * positiveMass r (a + c) b c (n + 1) +
      UrnWaiting.continuation a b c 0 * positiveMass (r + 1) a (b + c) c n := by
  have hd : (0 : ℝ) < a + b := by positivity
  have hmarked : (0 : ℝ) ≤ a / (a + b) := by positivity
  have hunmarked : (0 : ℝ) ≤ b / (a + b) := by positivity
  simp only [positiveMass]
  rw [coefficient_recurrence,
    ENNReal.ofReal_add (mul_nonneg hmarked (coefficient_nonneg r (a + c) b c (n + 1)))
      (mul_nonneg hunmarked (coefficient_nonneg (r + 1) a (b + c) c n)),
    ENNReal.ofReal_mul hmarked, ENNReal.ofReal_mul hunmarked,
    stop_probability a b c ha, continue_probability a b c ha,
    ENNReal.ofReal_div_of_pos hd, ENNReal.ofReal_div_of_pos hd]
  simp [ENNReal.ofReal_add (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

/-- The inverse-urn law has the canonical beta-negative-binomial rising-product mass. -/
theorem mass_positive (r a b c n : ℕ) (ha : 0 < a) :
    law (r + 1) a b c ha {n} = positiveMass r a b c n := by
  induction r generalizing a b n with
  | zero =>
    induction n generalizing a b with
    | zero => rw [mass_zero, positiveMass_zero _ _ _ _ ha]
    | succ n ih =>
      have hzero : law 0 (a + c) b c (by omega) {n + 1} = 0 := by simp [law]
      rw [mass_succ_recurrence, hzero, mul_zero, zero_add, ih]
      exact (positiveMass_one_step a b c n ha).symm
  | succ r ih =>
    induction n generalizing a b with
    | zero => rw [mass_zero, positiveMass_zero _ _ _ _ ha]
    | succ n ihn =>
      rw [mass_succ_recurrence, ih, ihn]
      exact (positiveMass_recurrence r a b c n ha).symm

end

end SampLib.InverseUrn
