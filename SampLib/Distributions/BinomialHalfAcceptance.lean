import SampLib.Distributions.BinomialHalfProposal

/-! # Exact cancellation in the half-binomial rejection step -/

open scoped ENNReal

namespace SampLib.BinomialHalfProposal

noncomputable section

open BinomialHalfEnvelope

/-- The two signed halves meet between offsets zero and minus one. -/
theorem candidate_bounds (n : ℕ) (t : ℕ × (Fin (width n) × Bool))
    (h0 : 0 ≤ candidate n t) (hn : candidate n t ≤ n) :
    (candidate n t).toNat ≤ n ∧
      t.1 * width n ≤ Nat.dist (candidate n t).toNat (n / 2) := by
  obtain ⟨block, rank, sign⟩ := t
  have hrank := rank.isLt
  have hcast : ((candidate n (block, rank, sign)).toNat : ℤ) =
      candidate n (block, rank, sign) := Int.toNat_of_nonneg h0
  constructor
  · omega
  · cases sign
    · simp only [candidate, Bool.false_eq_true, ↓reduceIte] at h0 hcast hn ⊢
      rw [Nat.dist_eq_sub_of_le (by omega)]
      push_cast at hcast
      omega
    · simp only [candidate, ↓reduceIte] at h0 hcast hn ⊢
      rw [Nat.dist_eq_sub_of_le_right (by omega)]
      push_cast at hcast
      omega

/-- Conditional probability of accepting a valid candidate. -/
def acceptance (n : ℕ) (t : ℕ × (Fin (width n) × Bool)) : ℝ :=
  if 0 ≤ candidate n t ∧ candidate n t ≤ n then
    (Nat.choose n (candidate n t).toNat * width n : ℕ) /
      (2 : ℝ) ^ (n + 2 - t.1)
  else 0

theorem acceptance_mem (n : ℕ) (hn : Even n)
    (t : ℕ × (Fin (width n) × Bool)) : acceptance n t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold acceptance
  split_ifs with hvalid
  · have hb := candidate_bounds n t hvalid.1 hvalid.2
    have h := acceptance_bound hn hb.1 hb.2
    constructor
    · positivity
    · apply (div_le_one (by positivity : 0 < (2 : ℝ) ^ (n + 2 - t.1))).mpr
      exact_mod_cast h
  · exact ⟨le_rfl, zero_le_one⟩

/-- Proposal mass and acceptance cancel the block, rank, and sign factors. -/
theorem accepted_coefficient (n k block : ℕ) (hblock : block ≤ n + 2) :
    ((1 / 2 : ℝ) ^ (block + 2) / width n) *
      ((Nat.choose n k * width n : ℕ) / (2 : ℝ) ^ (n + 2 - block)) =
        (Nat.choose n k : ℝ) / 2 ^ (n + 4) := by
  have hw : (width n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (width_pos n)
  have he : block + 2 + (n + 2 - block) = n + 4 := by omega
  rw [one_div_pow]
  push_cast
  field_simp
  rw [← he, pow_add]
  ring

/-- The accepted subprobability at a candidate is independent of its proposal block. -/
theorem accepted_atom (n : ℕ) (hn : Even n)
    (t : ℕ × (Fin (width n) × Bool)) :
    ENNReal.ofReal (acceptance n t) * law n {t} =
      if 0 ≤ candidate n t ∧ candidate n t ≤ n then
        ENNReal.ofReal ((Nat.choose n (candidate n t).toNat : ℝ) / 2 ^ (n + 4))
      else 0 := by
  rw [law_singleton]
  unfold acceptance
  split_ifs with hvalid
  · have hb := candidate_bounds n t hvalid.1 hvalid.2
    have hblock : t.1 ≤ n + 2 := by
      have := block_le_middle hn hb.1 hb.2
      omega
    rw [← ENNReal.ofReal_mul (by positivity), mul_comm,
      accepted_coefficient n (candidate n t).toNat t.1 hblock]
  · simp

end

end SampLib.BinomialHalfProposal
