module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic

@[expose] public section

/-! # Finite barriers for a fair first-passage walk

The escape credit `k/B` is harmonic and reaches one at the upper barrier. The
quadratic potential `k(B-k)+1` loses one per interior step, giving a uniform
amplification factor on every fixed interval without a finite global mean runtime.
-/

open Filter
open scoped NNReal Topology

namespace SampLib.MinimumComplement.Barrier

noncomputable section

def escape (B k : ℕ) : ℝ≥0 := (k : ℝ≥0) / B

def potential (B k : ℕ) : ℝ≥0 := (k * (B - k) + 1 : ℕ)

def amplifier (B : ℕ) : ℝ≥0 := ((B : ℝ≥0) ^ 2 + 1) / (B : ℝ≥0) ^ 2

theorem escape_at_barrier (B : ℕ) (hB : 0 < B) : escape B B = 1 := by
  exact div_self (by exact_mod_cast hB.ne')

theorem escape_le_one (B k : ℕ) (hB : 0 < B) (hk : k ≤ B) : escape B k ≤ 1 := by
  apply (div_le_one (by exact_mod_cast hB)).mpr
  exact_mod_cast hk

theorem escape_harmonic (B k : ℕ) (hk : 0 < k) :
    (escape B (k - 1) + escape B (k + 1)) / 2 = escape B k := by
  apply NNReal.coe_injective
  simp only [escape, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat]
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_add, Nat.cast_one]
  ring

theorem one_le_potential (B k : ℕ) : 1 ≤ potential B k := by
  unfold potential
  exact_mod_cast (show 1 ≤ k * (B - k) + 1 by omega)

theorem potential_one (B : ℕ) (hB : 0 < B) : potential B 1 = B := by
  unfold potential
  congr 1
  omega

theorem potential_le_max (B k : ℕ) (hk : k ≤ B) :
    potential B k ≤ (B : ℝ≥0) ^ 2 + 1 := by
  have h := Nat.mul_le_mul hk (Nat.sub_le B k)
  unfold potential
  exact_mod_cast (show k * (B - k) + 1 ≤ B ^ 2 + 1 by nlinarith)

private theorem potential_real (B k : ℕ) (hk : k ≤ B) :
    (potential B k : ℝ) = (k : ℝ) * ((B : ℝ) - k) + 1 := by
  change ((k * (B - k) + 1 : ℕ) : ℝ) = _
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_sub hk]

/-- The bounded quadratic potential decreases by exactly one in conditional expectation. -/
theorem potential_step (B k : ℕ) (hk : 0 < k) (hkB : k < B) :
    ((potential B (k - 1) : ℝ) + potential B (k + 1)) / 2 = potential B k - 1 := by
  rw [potential_real B (k - 1) (by omega), potential_real B (k + 1) (by omega),
    potential_real B k hkB.le]
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_add, Nat.cast_one]
  ring

theorem one_lt_amplifier (B : ℕ) (hB : 0 < B) : 1 < amplifier B := by
  apply (lt_div_iff₀ (show (0 : ℝ≥0) < (B : ℝ≥0) ^ 2 by positivity)).mpr
  simp

/-- The amplified credits for the two recursive children fit the current potential. -/
theorem amplification_bound (B k : ℕ) (hk : 0 < k) (hkB : k < B) :
    amplifier B / 2 * (potential B (k - 1) + potential B (k + 1)) ≤ potential B k := by
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat]
  calc
    _ = (amplifier B : ℝ) * (((potential B (k - 1) : ℝ) + potential B (k + 1)) / 2) := by
      ring
    _ = (amplifier B : ℝ) * ((potential B k : ℝ) - 1) := by rw [potential_step B k hk hkB]
    _ ≤ (potential B k : ℝ) := by
      have hmax : (potential B k : ℝ) ≤ (B : ℝ) ^ 2 + 1 := by
        exact_mod_cast potential_le_max B k hkB.le
      have hBB : (0 : ℝ) < (B : ℝ) ^ 2 := by have : 0 < B := hk.trans hkB; positivity
      simp only [amplifier, NNReal.coe_div, NNReal.coe_add, NNReal.coe_pow,
        NNReal.coe_natCast, NNReal.coe_one]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hBB).mpr
      nlinarith

/-- An arbitrarily small initial escape credit is obtained by moving the upper barrier. -/
theorem exists_barrier (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℕ, 2 ≤ B ∧ (escape B 1 : ℝ) ≤ ε := by
  have he := (tendsto_order.mp
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).2 ε hε
  obtain ⟨B, hB, hBe⟩ := ((eventually_ge_atTop 2).and he).exists
  exact ⟨B, hB, by simpa [escape] using hBe.le⟩

end

end SampLib.MinimumComplement.Barrier
