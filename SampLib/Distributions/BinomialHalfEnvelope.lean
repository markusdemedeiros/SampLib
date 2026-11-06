module

public import SampLib.Distributions.BinomialHalfEnvelopeDecay
public import Mathlib.Data.Nat.Dist

@[expose] public section

/-! # The exact acceptance bound for half-binomial rejection

The distance from the middle determines a valid block on either side. The
coefficient envelope pays for the source's integer denominator, including the
small even inputs for which no noncentral block fits inside the support.
-/

namespace SampLib.BinomialHalfEnvelope

noncomputable section

theorem distance_le_middle (m k : ℕ) (hk : k ≤ 2 * m) : Nat.dist k m ≤ m := by
  by_cases hkm : k ≤ m
  · rw [Nat.dist_eq_sub_of_le hkm]
    omega
  · rw [Nat.dist_eq_sub_of_le_right (by omega : m ≤ k)]
    omega

theorem upperCoefficient_dist (m k : ℕ) (hk : k ≤ 2 * m) :
    upperCoefficient m (Nat.dist k m) = (Nat.choose (2 * m) k : ℝ) := by
  by_cases hkm : k ≤ m
  · rw [Nat.dist_eq_sub_of_le hkm]
    unfold upperCoefficient
    rw [show m + (m - k) = 2 * m - k by omega, Nat.choose_symm hk]
  · rw [Nat.dist_eq_sub_of_le_right (by omega : m ≤ k)]
    unfold upperCoefficient
    rw [show m + (k - m) = k by omega]

/-- Valid candidates force the proposal block and its source exponent to be bounded. -/
theorem block_le_middle {n k block : ℕ} (hn : Even n) (hk : k ≤ n)
    (hblock : block * width n ≤ Nat.dist k (n / 2)) : block ≤ n / 2 := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hn
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at hblock ⊢
  have hb : block ≤ block * width (2 * m) :=
    Nat.le_mul_of_pos_right _ (width_pos _)
  exact hb.trans (hblock.trans (distance_le_middle m k hk))

/-- The rational acceptance coin is in `[0,1]` for every valid source candidate. -/
theorem acceptance_bound {n k block : ℕ} (hn : Even n) (hk : k ≤ n)
    (hblock : block * width n ≤ Nat.dist k (n / 2)) :
    Nat.choose n k * width n ≤ 2 ^ (n + 2 - block) := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hn
  have hb : block ≤ 2 * m + 2 := by
    have := block_le_middle (by exact even_iff_exists_two_mul.mpr ⟨m, rfl⟩) hk hblock
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at this
    omega
  rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at hblock
  have h := point_envelope m block (Nat.dist k m) hblock (distance_le_middle m k hk)
  rw [upperCoefficient_dist m k hk] at h
  have hpow : 4 * (2 : ℝ) ^ (2 * m) = (2 : ℝ) ^ (2 * m + 2) := by
    norm_num [pow_add, mul_comm]
  rw [hpow] at h
  have hmul : Nat.choose (2 * m) k * width (2 * m) * 2 ^ block ≤ 2 ^ (2 * m + 2) := by
    exact_mod_cast h
  apply Nat.le_of_mul_le_mul_right _ (by positivity : 0 < 2 ^ block)
  calc
    _ ≤ 2 ^ (2 * m + 2) := hmul
    _ = 2 ^ (2 * m + 2 - block) * 2 ^ block := by
      rw [← pow_add, Nat.sub_add_cancel hb]

end

end SampLib.BinomialHalfEnvelope
