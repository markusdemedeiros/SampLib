import SampLib.Weighted.Laws.KnuthYaoColumns
import SampLib.Weighted.Support.PowerOfTwoCeiling

/-! # Finite binary columns of the fast loaded dice roller

Padding the integer weights to a power of two gives a finite DDG matrix.
The source's descending place values read exactly its successive binary columns.
-/

namespace SampLib.FldrDyadic

/-- The source's place value at zero-based column `d`. -/
def place (k d : ℕ) : ℕ := 2 ^ k / 2 ^ (d + 1)

@[simp] theorem place_zero (k : ℕ) : place k 0 = 2 ^ k / 2 := by simp [place]

theorem place_eq (k d : ℕ) (hd : d < k) : place k d = 2 ^ (k - (d + 1)) := by
  have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : d + 1 ≤ k)]
  rw [place, hpow, Nat.mul_div_cancel _ (by positivity)]

theorem place_pos (k d : ℕ) (hd : d < k) : 0 < place k d := by
  rw [place_eq k d hd]
  positivity

@[simp] theorem place_half (k d : ℕ) : place k d / 2 = place k (d + 1) := by
  simp only [place, Nat.div_div_eq_div_mul, pow_succ]

theorem place_vanishes (k d : ℕ) (hd : k ≤ d) : place k d = 0 := by
  apply Nat.div_eq_of_lt
  exact Nat.pow_lt_pow_right (by omega : 1 < 2) (by omega)

/-- The digit computed by division by `place` is the corresponding binary matrix bit. -/
theorem digit (w k d : ℕ) (hd : d < k) :
    w / place k d % 2 = (w * 2 ^ (d + 1) / 2 ^ k) % 2 := by
  have hpow : 2 ^ k = 2 ^ (k - (d + 1)) * 2 ^ (d + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : d + 1 ≤ k)]
  rw [place_eq k d hd, hpow, Nat.mul_div_mul_right _ _ (by positivity)]

theorem column {n : ℕ} (w : Fin n → ℕ) (k d : ℕ) (hd : d < k) (i : Fin n) :
    w i / place k d % 2 = KnuthYaoColumns.column w (2 ^ k) d i := by
  rw [digit _ k d hd]
  simp only [KnuthYaoColumns.column, KnuthYaoColumns.quotient, mul_comm (w i)]

/-- At the matrix's finite height every dyadic row has exhausted its remainder. -/
theorem alive_zero {n : ℕ} (w : Fin n → ℕ) (k d : ℕ)
    (htotal : ∑ i, w i = 2 ^ k) (hd : k ≤ d) : KnuthYaoColumns.alive w (2 ^ k) d = 0 := by
  have hrem : ∑ i, KnuthYaoColumns.remainder w (2 ^ k) d i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (pow_dvd_pow 2 hd) (w i))
  have h := KnuthYaoColumns.sum_remainder (by positivity : 0 < 2 ^ k) htotal d
  rw [hrem] at h
  have hpos : 0 < 2 ^ k := by positivity
  nlinarith

/-- The final artificial row represents rejection and restart. -/
def padded (weights : List ℕ) (P : ℕ) : List ℕ := weights ++ [P - weights.sum]

theorem sum_padded (weights : List ℕ) (P : ℕ) (hP : weights.sum ≤ P) :
    (padded weights P).sum = P := by
  simp only [padded, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  exact Nat.add_sub_of_le hP

theorem padded_lt (weights : List ℕ) (P : ℕ) (hpos : 0 < weights.sum)
    (hP : weights.sum ≤ P) (hproper : ∀ w ∈ weights, w < weights.sum) :
    ∀ w ∈ padded weights P, w < P := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (hproper w hw).trans_le hP
  · have hw' : w = P - weights.sum := by simpa only [List.mem_singleton] using hw
    subst w
    exact Nat.sub_lt (hpos.trans_le hP) hpos

end SampLib.FldrDyadic
