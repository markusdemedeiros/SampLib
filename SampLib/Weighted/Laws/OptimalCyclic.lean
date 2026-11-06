module

public import SampLib.Weighted.Laws.OptimalEncoding
public import SampLib.Weighted.Laws.BinaryTail

@[expose] public section

/-! # Exact row masses of the finite cyclic binary matrix

The actual column sequence reads the prefix once and then repeats the last block.
Scaled binary quotients telescope through the first pass. Comparing the identities
at the end of the prefix and the end of the block recovers the row's numerator.
-/

namespace SampLib.OptimalCyclic

noncomputable section

open OptimalEncoding

/-- The absolute depth selects the same finite column as the source's jump back to `l`. -/
def column (k l d : ℕ) : ℕ := if d < l then d else l + (d - l) % (k - l)

theorem column_initial {k l d : ℕ} (hl : l < k) (hd : d < k) : column k l d = d := by
  unfold column
  split_ifs with hdl
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega : d - l < k - l)]
    omega

theorem column_lt {k l : ℕ} (hl : l < k) (d : ℕ) : column k l d < k := by
  unfold column
  split_ifs with hdl
  · omega
  · have h := Nat.mod_lt (d - l) (by omega : 0 < k - l)
    omega

private theorem mod_succ (a p : ℕ) (hp : 0 < p) :
    (a + 1) % p = if a % p + 1 = p then 0 else a % p + 1 := by
  rw [← Nat.mod_add_mod a p 1]
  have hr := Nat.mod_lt a hp
  split_ifs with heq
  · simp only [heq, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- One source iteration either advances one column or jumps from the last column to `l`. -/
theorem column_succ {k l : ℕ} (hl : l < k) (d : ℕ) :
    column k l (d + 1) = if column k l d + 1 = k then l else column k l d + 1 := by
  by_cases hdl : d < l
  · rw [column_initial hl (by omega : d + 1 < k), column_initial hl (by omega : d < k),
      ite_eq_right (by omega : d + 1 ≠ k)]
  · unfold column
    rw [ite_eq_right hdl, ite_eq_right (by omega : ¬d + 1 < l),
      show d + 1 - l = (d - l) + 1 by omega, mod_succ _ _ (by omega : 0 < k - l)]
    have hr := Nat.mod_lt (d - l) (by omega : 0 < k - l)
    split_ifs <;> omega

/-- The continuation after one whole block equals the continuation after the prefix. -/
theorem column_cycle {k l : ℕ} (hl : l < k) (n : ℕ) :
    column k l (k + n) = column k l (l + n) := by
  unfold column
  rw [ite_eq_right (by omega : ¬k + n < l), ite_eq_right (by omega : ¬l + n < l),
    show k + n - l = (k - l) + n by omega, Nat.add_mod_left,
    show l + n - l = n by omega]

/-- The exact bit inspected by the integer division and remainder in the source scan. -/
def bit (k l E d : ℕ) : ℕ := E / 2 ^ (k - 1 - column k l d) % 2

theorem bit_le_one (k l E d : ℕ) : bit k l E d ≤ 1 := by
  have h := Nat.mod_lt (E / 2 ^ (k - 1 - column k l d)) (by decide : 0 < 2)
  exact Nat.le_of_lt_succ h

/-- Conditional remaining mass of one row at an absolute depth. -/
def tail (k l E : ℕ) : ℕ → ℝ := BinaryTail.value (bit k l E)

theorem tail_nonneg (k l E d : ℕ) : 0 ≤ tail k l E d := BinaryTail.nonneg _ _

theorem tail_le_one (k l E d : ℕ) : tail k l E d ≤ 1 :=
  BinaryTail.le_one _ (bit_le_one k l E) d

theorem tail_succ (k l E d : ℕ) :
    2 * tail k l E d = (bit k l E d : ℝ) + tail k l E (d + 1) :=
  BinaryTail.succ _ (bit_le_one k l E) d

theorem tail_cycle {k l : ℕ} (hl : l < k) (E : ℕ) : tail k l E k = tail k l E l := by
  unfold tail BinaryTail.value
  congr 1
  funext n
  simp only [bit, column_cycle hl]

/-- Comparing the scaled prefix and block equations gives the cyclic rational row mass. -/
theorem tail_zero {k l E : ℕ} (hl : l < k) (hE : E < 2 ^ k) :
    tail k l E 0 = (decode (2 ^ (k - l)) E : ℝ) / denominator k l := by
  have hbits c (hc : c < k) : bit k l E c = E / 2 ^ (k - 1 - c) % 2 := by
    rw [bit, column_initial hl hc]
  have hk := BinaryTail.scaled_prefix _ (bit_le_one k l E) E k hE hbits k le_rfl
  have hp := BinaryTail.scaled_prefix _ (bit_le_one k l E) E k hE hbits l hl.le
  change (2 : ℝ) ^ k * tail k l E 0 = (E / 2 ^ (k - k) : ℕ) + tail k l E k at hk
  change (2 : ℝ) ^ l * tail k l E 0 = (E / 2 ^ (k - l) : ℕ) + tail k l E l at hp
  simp only [Nat.sub_self, pow_zero, Nat.div_one, tail_cycle hl] at hk
  have hP : 1 < 2 ^ (k - l) := one_lt_pow₀ (by decide) (by omega)
  have hdecode : decode (2 ^ (k - l)) E + E / 2 ^ (k - l) = E := by
    unfold decode
    have h := Nat.div_add_mod E (2 ^ (k - l))
    calc
      _ = (E / 2 ^ (k - l)) * ((2 ^ (k - l) - 1) + 1) + E % 2 ^ (k - l) := by ring
      _ = (E / 2 ^ (k - l)) * 2 ^ (k - l) + E % 2 ^ (k - l) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ (k - l))]
      _ = E := by simpa only [Nat.mul_comm] using h
  have hdecode' : (decode (2 ^ (k - l)) E : ℝ) + (E / 2 ^ (k - l) : ℕ) = E := by
    exact_mod_cast hdecode
  have hD : (denominator k l : ℝ) = (2 : ℝ) ^ k - 2 ^ l := by
    rw [denominator, Nat.cast_sub (Nat.pow_le_pow_right (by decide) hl.le)]
    norm_cast
  have hDpos : 0 < denominator k l := by
    rw [denominator_factor hl.le]
    exact Nat.mul_pos (by positivity) (by omega)
  apply (eq_div_iff (by exact_mod_cast hDpos.ne' : (denominator k l : ℝ) ≠ 0)).mpr
  rw [hD]
  nlinarith

/-- The repaired encoder has exactly its specified probability, including zero and one. -/
theorem encoded_tail_zero {k l m : ℕ} (hl : l < k) (hm : m ≤ denominator k l) :
    tail k l (binary k l m) 0 = (m : ℝ) / denominator k l := by
  rw [tail_zero hl (binary_lt hl hm), decode_binary hl hm]

end

end SampLib.OptimalCyclic
