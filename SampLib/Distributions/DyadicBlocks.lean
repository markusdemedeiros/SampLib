module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! # The unique dyadic block of each positive integer

Level `l` consists of the integers `2^l,…,2^(l+1)-1`. Removing the leading bit
identifies a positive integer with its level and its rank in that finite block.
-/

namespace SampLib.DyadicBlocks

abbrev Block := Σ l : ℕ, Fin (2 ^ l)

def value (t : Block) : ℕ := 2 ^ t.1 + t.2

def index (t : Block) : ℕ := value t - 1

theorem value_pos (t : Block) : 0 < value t := by
  unfold value
  positivity

theorem index_succ (t : Block) : index t + 1 = value t := by
  unfold index
  have := value_pos t
  omega

def level (k : ℕ) : ℕ := Nat.log 2 (k + 1)

theorem lower_bound (k : ℕ) : 2 ^ level k ≤ k + 1 :=
  Nat.pow_log_le_self 2 (Nat.succ_ne_zero k)

theorem upper_bound (k : ℕ) : k + 1 < 2 ^ level k * 2 := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (k + 1)
  simpa only [level, pow_succ] using h

def rank (k : ℕ) : Fin (2 ^ level k) :=
  ⟨k + 1 - 2 ^ level k, by have := lower_bound k; have := upper_bound k; omega⟩

def inverse (k : ℕ) : Block := ⟨level k, rank k⟩

theorem inverse_index (t : Block) : inverse (index t) = t := by
  obtain ⟨l, r⟩ := t
  have hv : index ⟨l, r⟩ + 1 = 2 ^ l + r := index_succ ⟨l, r⟩
  have hl : level (index ⟨l, r⟩) = l := by
    unfold level
    rw [hv]
    apply (Nat.log_eq_iff (Or.inr ⟨by decide, by positivity⟩)).mpr
    constructor
    · omega
    · rw [pow_succ]
      have := r.isLt
      omega
  apply Sigma.ext hl
  apply (Fin.heq_ext_iff (congrArg (fun l : ℕ => 2 ^ l) hl)).mpr
  change index ⟨l, r⟩ + 1 - 2 ^ level (index ⟨l, r⟩) = r
  rw [hl, hv]
  omega

theorem index_inverse (k : ℕ) : index (inverse k) = k := by
  change 2 ^ level k + (k + 1 - 2 ^ level k) - 1 = k
  have := lower_bound k
  omega

/-- The leading-bit decomposition, indexed by the positive value minus one. -/
def equiv : Block ≃ ℕ where
  toFun := index
  invFun := inverse
  left_inv := inverse_index
  right_inv := index_inverse

theorem value_eq (t : Block) : value t = equiv t + 1 := (index_succ t).symm

/-- The block construction introduces no repeated values. -/
theorem value_injective : Function.Injective value := by
  intro t u h
  apply equiv.injective
  exact congrArg (· - 1) h

end SampLib.DyadicBlocks
