import SampLib.Distributions.OptimalCredits

/-! # The categorical law of an arbitrary cyclic probability table

A row's scanned bits read only its low `k` bits, whose cyclic expansion has the integer
numerator `weight` over `2^k - 2^l`. The source restarts at the rejected label, so the
output law keeps the remaining numerators. Rejection has mass `B/D < 1`; the factor
`1 + A/D` (with `A = D - B` accepted mass) amplifies retry credit while `B(1 + A/D) ≤ D`.
-/

open Finset MeasureTheory
open scoped NNReal ENNReal

namespace SampLib.OptimalTable

noncomputable section

open OptimalCyclic OptimalEncoding

variable {n : ℕ}

/-- Numerator of a row's cyclic mass over `denominator k l`. -/
def weight (k l E : ℕ) : ℕ := decode (2 ^ (k - l)) (E % 2 ^ k)

/-- Numerators of the labels returned without a restart. -/
def accepted (rows : Fin n → ℕ) (k l : ℕ) (rejected : ℤ) : List ℕ :=
  List.ofFn fun i => if (i : ℤ) = rejected then 0 else weight k l (rows i)

/-- Accepted numerator mass, which normalizes the output law. -/
abbrev acceptedMass (rows : Fin n → ℕ) (k l : ℕ) (rejected : ℤ) : ℕ :=
  (accepted rows k l rejected).sum

/-- Retry amplification `1 + A/D`. -/
def factor (rows : Fin n → ℕ) (k l : ℕ) (rejected : ℤ) : ℝ≥0 :=
  1 + (acceptedMass rows k l rejected : ℝ≥0) / denominator k l

theorem one_lt_factor (rows : Fin n → ℕ) {k l : ℕ} (hl : l < k) (rejected : ℤ)
    (hA : 0 < acceptedMass rows k l rejected) : 1 < factor rows k l rejected := by
  have hD : (0 : ℝ≥0) < denominator k l := by exact_mod_cast denominator_pos hl
  unfold factor
  exact lt_add_of_pos_right 1 (div_pos (by exact_mod_cast hA) hD)

/-- The scan inspects only bits below `2^k`. -/
private theorem bit_mod {k l : ℕ} (hl : l < k) (E d : ℕ) :
    bit k l (E % 2 ^ k) d = bit k l E d := by
  have hc := column_lt hl d
  unfold bit
  set j := k - 1 - column k l d
  rw [show 2 ^ k = 2 ^ j * 2 ^ (k - j) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self 2 (by omega))]

theorem tail_zero_eq {k l : ℕ} (hl : l < k) (E : ℕ) :
    tail k l E 0 = (weight k l E : ℝ) / denominator k l := by
  have h : tail k l E 0 = tail k l (E % 2 ^ k) 0 := by
    unfold tail
    congr 1
    funext d
    exact (bit_mod hl E d).symm
  rw [h, tail_zero hl (Nat.mod_lt _ (by positivity))]
  rfl

/-- Numerators summing to the denominator give total root mass one. -/
theorem root_mass (rows : Fin n → ℕ) {k l : ℕ} (hl : l < k)
    (hroot : ∑ i, weight k l (rows i) = denominator k l) :
    ∑ i, tail k l (rows i) 0 = 1 := by
  simp_rw [tail_zero_eq hl]
  rw [← sum_div, ← Nat.cast_sum, hroot]
  exact div_self (by exact_mod_cast (denominator_pos hl).ne')

private theorem fraction_zero {k l : ℕ} (hl : l < k) (E : ℕ) :
    (fraction k l E 0 : ℝ≥0∞) = (weight k l E : ℝ≥0∞) / denominator k l := by
  have hD : (denominator k l : ℝ≥0) ≠ 0 := by exact_mod_cast (denominator_pos hl).ne'
  have h : fraction k l E 0 = (weight k l E : ℝ≥0) / denominator k l := by
    apply NNReal.eq
    rw [NNReal.coe_div]
    exact tail_zero_eq hl E
  rw [h, ENNReal.coe_div hD]
  simp

/-- Root row credit pays the output law's expectation plus one auxiliary credit. -/
theorem restart_expectation (rows : Fin n → ℕ) {k l : ℕ} (hl : l < k) (rejected : ℤ)
    (hroot : ∑ i, weight k l (rows i) = denominator k l)
    (hA : 0 < acceptedMass rows k l rejected) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    rowCredit rows k l 0 (leafCredit rejected
      ((∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)) +
        factor rows k l rejected * ε) F) ≤
      (∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)) + ε := by
  let C := ∫⁻ i, F i ∂WeightedChoice.law (accepted rows k l rejected)
  let D := denominator k l
  let A := acceptedMass rows k l rejected
  let b : Fin n → ℕ := fun i => if (i : ℤ) = rejected then weight k l (rows i) else 0
  let B := ∑ i, b i
  have hD : 0 < D := denominator_pos hl
  have hD0 : (D : ℝ≥0∞) ≠ 0 := by exact_mod_cast hD.ne'
  have hDtop : (D : ℝ≥0∞) ≠ ∞ := by finiteness
  have hAB : A + B = D := by
    simp only [A, B, b, acceptedMass, accepted, List.sum_ofFn, ← sum_add_distrib]
    show _ = denominator k l
    rw [← hroot]
    exact sum_congr rfl (fun i _ => by split_ifs <;> simp)
  have hcredit : WeightedChoice.weightedSum (accepted rows k l rejected) F = (A : ℝ≥0∞) * C := by
    dsimp [C]
    rw [WeightedChoice.lintegral_law,
      ENNReal.mul_div_cancel (by exact_mod_cast hA.ne') (by finiteness)]
  have hrow : rowCredit rows k l 0 (leafCredit rejected (C + factor rows k l rejected * ε) F) =
      (WeightedChoice.weightedSum (accepted rows k l rejected) F +
        (B : ℝ≥0∞) * (C + factor rows k l rejected * ε)) / D := by
    let R := C + factor rows k l rejected * ε
    have hterm (i : Fin n) : (weight k l (rows i) : ℝ≥0∞) / D * leafCredit rejected R F i =
        (((if (i : ℤ) = rejected then 0 else weight k l (rows i) : ℕ) : ℝ≥0∞) * F i +
          (b i : ℝ≥0∞) * R) / D := by
      by_cases hi : (i : ℤ) = rejected <;>
        simp [b, leafCredit, hi, ENNReal.div_eq_inv_mul, mul_assoc]
    simp only [rowCredit, fraction_zero hl]
    rw [sum_congr rfl (fun i _ => hterm i), ← ENNReal.sum_div, sum_add_distrib, accepted,
      KnuthYaoColumns.weightedSum_ofFn, ← sum_mul, ← Nat.cast_sum]
  -- Rejection mass times the amplification never exceeds the denominator.
  have hbudget : (B : ℝ≥0) * factor rows k l rejected ≤ D := by
    have hD' : (0 : ℝ≥0) < D := by exact_mod_cast hD
    have hBA : (B : ℝ≥0) * A / D ≤ A := by
      rw [div_le_iff₀ hD', mul_comm]
      gcongr
      exact_mod_cast (show B ≤ D by omega)
    calc
      _ = (B : ℝ≥0) + B * A / D := by unfold factor; rw [mul_add, mul_one, mul_div_assoc]
      _ ≤ B + A := by gcongr
      _ = D := by exact_mod_cast (show B + A = D by omega)
  have hbudget' : (B : ℝ≥0∞) * factor rows k l rejected ≤ D := by exact_mod_cast hbudget
  rw [hrow, hcredit, ENNReal.div_le_iff hD0 hDtop]
  calc
    _ = ((A + B : ℕ) : ℝ≥0∞) * C + ((B : ℝ≥0∞) * factor rows k l rejected) * ε := by
      push_cast
      ring
    _ ≤ (D : ℝ≥0∞) * C + D * ε := by
      rw [hAB]
      gcongr
    _ = _ := by ring

end

end SampLib.OptimalTable
