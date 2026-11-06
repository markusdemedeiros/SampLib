import SampLib.Weighted.Laws.OptimalCyclic
import SampLib.Weighted.Laws.KnuthYaoCredits

/-! # Live ranks and expectation conservation for the cyclic matrix

The remaining row masses sum to the live-rank count. Their unit-interval bounds
therefore give a uniform bound by the number of rows. The same one-bit identity
preserves arbitrary nonnegative extended-real continuation credit.
-/

open Finset
open scoped NNReal ENNReal

namespace SampLib.OptimalCyclic

noncomputable section

variable {n : ℕ}

/-- A rejection leaf receives the budget of the caller's restart continuation. -/
def leafCredit (rejected : ℤ) (restartCredit : ℝ≥0∞) (F : ℕ → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ :=
  if (i : ℤ) = rejected then restartCredit else F i

/-- The source's ordered bits at an absolute depth. -/
def columns (E : Fin n → ℕ) (k l d : ℕ) : List ℕ := List.ofFn (fun i => bit k l (E i) d)

/-- One live root, followed by doubling and consuming the current column's leaves. -/
def alive (E : Fin n → ℕ) (k l : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => 2 * alive E k l d - (columns E k l d).sum

private theorem sum_tail_succ (E : Fin n → ℕ) (k l d : ℕ) :
    2 * (∑ i, tail k l (E i) d) =
      ((columns E k l d).sum : ℝ) + ∑ i, tail k l (E i) (d + 1) := by
  rw [mul_sum]
  calc
    _ = ∑ i, ((bit k l (E i) d : ℝ) + tail k l (E i) (d + 1)) :=
      sum_congr rfl (fun i _ => tail_succ k l (E i) d)
    _ = _ := by simp only [sum_add_distrib, columns, List.sum_ofFn, Nat.cast_sum]

/-- The arithmetic live count agrees exactly with the sum of the remaining row masses. -/
theorem sum_tail_eq_alive (E : Fin n → ℕ) (k l : ℕ)
    (hroot : ∑ i, tail k l (E i) 0 = 1) (d : ℕ) :
    (∑ i, tail k l (E i) d) = (alive E k l d : ℝ) := by
  induction d with
  | zero => simpa only [alive, Nat.cast_one] using hroot
  | succ d ih =>
    have hs := sum_tail_succ E k l d
    have hn : 0 ≤ ∑ i, tail k l (E i) (d + 1) :=
      sum_nonneg (fun i _ => tail_nonneg k l (E i) (d + 1))
    have hle : ((columns E k l d).sum : ℝ) ≤ 2 * (alive E k l d : ℝ) := by
      rw [ih] at hs
      linarith
    have hle' : (columns E k l d).sum ≤ 2 * alive E k l d := by exact_mod_cast hle
    simp only [alive, Nat.cast_sub hle', Nat.cast_mul, Nat.cast_ofNat]
    linarith

/-- Twice the live ranks split into this column's leaves and the next live ranks. -/
theorem width (E : Fin n → ℕ) (k l : ℕ) (hroot : ∑ i, tail k l (E i) 0 = 1) (d : ℕ) :
    2 * alive E k l d = (columns E k l d).sum + alive E k l (d + 1) := by
  have h := sum_tail_succ E k l d
  rw [sum_tail_eq_alive E k l hroot d, sum_tail_eq_alive E k l hroot (d + 1)] at h
  exact_mod_cast h

/-- A row has at most unit remaining mass, even for the infinite all-ones expansion. -/
theorem alive_le (E : Fin n → ℕ) (k l : ℕ) (hroot : ∑ i, tail k l (E i) 0 = 1) (d : ℕ) :
    alive E k l d ≤ n := by
  have h : (alive E k l d : ℝ) ≤ n := by
    rw [← sum_tail_eq_alive E k l hroot d]
    calc
      _ ≤ ∑ _ : Fin n, (1 : ℝ) := sum_le_sum (fun i _ => tail_le_one k l (E i) d)
      _ = n := by simp
  exact_mod_cast h

/-- Finite nonnegative row masses are coerced only after their exact real recurrence. -/
def fraction (k l E d : ℕ) : ℝ≥0 := NNReal.mk (tail k l E d) (tail_nonneg k l E d)

theorem fraction_succ (k l E d : ℕ) :
    fraction k l E d = ((bit k l E d : ℝ≥0) + fraction k l E (d + 1)) / 2 := by
  apply NNReal.eq
  change tail k l E d = ((bit k l E d : ℝ) + tail k l E (d + 1)) / 2
  have h := tail_succ k l E d
  linarith

/-- Aggregate continuation credit remaining in the cyclic rows. -/
def rowCredit (E : Fin n → ℕ) (k l d : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, (fraction k l (E i) d : ℝ≥0∞) * F i

/-- Summing the one-bit row identity gives the complete CTE expectation step. -/
theorem row_expectation (E : Fin n → ℕ) (k l d : ℕ) (F : ℕ → ℝ≥0∞) :
    rowCredit E k l d F =
      (WeightedChoice.weightedSum (columns E k l d) F + rowCredit E k l (d + 1) F) / 2 := by
  simp only [rowCredit, columns, KnuthYaoColumns.weightedSum_ofFn]
  have hterm (i : Fin n) :
      (fraction k l (E i) d : ℝ≥0∞) * F i =
        ((bit k l (E i) d : ℝ≥0∞) * F i +
          (fraction k l (E i) (d + 1) : ℝ≥0∞) * F i) * (2 : ℝ≥0∞)⁻¹ := by
    rw [fraction_succ]
    push_cast
    simp only [div_eq_mul_inv, add_mul]
    ring
  simp_rw [hterm]
  rw [← sum_mul, sum_add_distrib]
  rfl

/-- Nonnegative row numerators summing to the denominator are individually valid. -/
private theorem weight_le (w : Fin n → ℕ) (D : ℕ) (h : ∑ i, w i = D) (i : Fin n) :
    w i ≤ D := by
  rw [← h]
  exact single_le_sum (fun j _ => Nat.zero_le (w j)) (mem_univ i)

/-- The repaired encodings, including zero and certain rows, start with total mass one. -/
theorem encoded_root {k l : ℕ} (hl : l < k) (w : Fin n → ℕ)
    (htotal : ∑ i, w i = OptimalEncoding.denominator k l) :
    ∑ i, tail k l (OptimalEncoding.binary k l (w i)) 0 = 1 := by
  simp_rw [encoded_tail_zero hl (weight_le w _ htotal _)]
  rw [← sum_div, ← Nat.cast_sum, htotal]
  have hD := OptimalEncoding.denominator_pos hl
  exact div_self (by exact_mod_cast hD.ne')

/-- At the root, arbitrary row credits are exactly the normalized requested weights. -/
theorem encoded_row_zero {k l : ℕ} (hl : l < k) (w : Fin n → ℕ)
    (htotal : ∑ i, w i = OptimalEncoding.denominator k l) (F : ℕ → ℝ≥0∞) :
    rowCredit (fun i => OptimalEncoding.binary k l (w i)) k l 0 F =
      (∑ i, (w i : ℝ≥0∞) * F i) / OptimalEncoding.denominator k l := by
  have hD := OptimalEncoding.denominator_pos hl
  have hf (i : Fin n) : fraction k l (OptimalEncoding.binary k l (w i)) 0 =
      (w i : ℝ≥0) / OptimalEncoding.denominator k l := by
    apply NNReal.eq
    change tail k l (OptimalEncoding.binary k l (w i)) 0 =
      (w i : ℝ) / OptimalEncoding.denominator k l
    exact encoded_tail_zero hl (weight_le w _ htotal i)
  simp only [rowCredit, hf,
    ENNReal.coe_div (by exact_mod_cast hD.ne' :
      (OptimalEncoding.denominator k l : ℝ≥0) ≠ 0)]
  push_cast
  simp only [div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- Concrete source rows give the same ordered column as their finite-index presentation. -/
theorem columns_list (rows : List ℕ) (k l d : ℕ) :
    columns rows.get k l d = rows.map (fun E => bit k l E d) := by
  unfold columns
  conv_rhs => rw [← List.ofFn_get rows, List.map_ofFn]
  rfl

/-- A fair source bit selects the two exact finite-cutoff scan credits. -/
theorem bit_expectation (E : Fin n → ℕ) (k l : ℕ) (F : ℕ → ℝ≥0∞)
    (h d rank : ℕ) :
    (∑ b ∈ range 2, DdgCredits.scan (columns E k l d) (2 * rank + b) F
      (DdgCredits.cutCredit (columns E k l) F h (d + 1))) / 2 =
        DdgCredits.cutCredit (columns E k l) F (h + 1) d rank := by
  simp [DdgCredits.cutCredit, sum_range_succ]

end

end SampLib.OptimalCyclic
