module

public import SampLib.Bernoulli.Laws.MinimumComplementBinomial
public import SampLib.Bernoulli.Laws.MinimumComplementCentral

@[expose] public section

/-! # Admissible rejection coefficients for the padded binomial stage

The ratio of the two binomial coefficients increases up to the middle and is
symmetric there. The central Wallis estimate therefore controls every source
coefficient, not merely the coefficient at the mode.
-/

namespace SampLib.MinimumComplement

noncomputable section

def chooseRatio (m r j : ℕ) : ℝ := (r.choose j : ℝ) / (2 * m + r).choose (m + j)

private theorem chooseRatio_symm (m r j : ℕ) (hj : j ≤ r) :
    chooseRatio m r (r - j) = chooseRatio m r j := by
  unfold chooseRatio
  rw [Nat.choose_symm hj]
  rw [← show 2 * m + r - (m + j) = m + (r - j) by omega,
    Nat.choose_symm (by omega : m + j ≤ 2 * m + r)]

private theorem denominator_pos (m r j : ℕ) (hj : j ≤ r) :
    (0 : ℝ) < ((2 * m + r).choose (m + j) : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : m + j ≤ 2 * m + r)

private theorem chooseRatio_step (m r j : ℕ) (hj : 2 * j + 1 ≤ r) :
    chooseRatio m r j ≤ chooseRatio m r (j + 1) := by
  have hnum : ((j : ℝ) + 1) * r.choose (j + 1) =
      ((r - j : ℕ) : ℝ) * r.choose j := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq r j)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm] using h
  have hden : ((m : ℝ) + j + 1) * (2 * m + r).choose (m + j + 1) =
      ((m + r - j : ℕ) : ℝ) * (2 * m + r).choose (m + j) := by
    have h := Nat.choose_succ_right_eq (2 * m + r) (m + j)
    rw [show 2 * m + r - (m + j) = m + r - j by omega] at h
    have h' := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_comm] using h'
  have hcoef : ((j : ℝ) + 1) * (m + r - j : ℕ) ≤
      ((r - j : ℕ) : ℝ) * ((m : ℝ) + j + 1) := by
    rw [Nat.cast_sub (by omega : j ≤ m + r), Nat.cast_add,
      Nat.cast_sub (by omega : j ≤ r)]
    have hgap : (0 : ℝ) ≤ r - 2 * j - 1 := by
      have h : ((2 * j + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hj
      push_cast at h
      linarith
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hgap]
  unfold chooseRatio
  simp only [Nat.add_assoc] at hden ⊢
  apply (div_le_div_iff₀ (denominator_pos m r j (by omega))
    (denominator_pos m r (j + 1) (by omega))).mpr
  apply (mul_le_mul_iff_right₀
    (show (0 : ℝ) < ((j : ℝ) + 1) * ((m : ℝ) + j + 1) by positivity)).mp
  calc
    _ = ((r.choose j : ℝ) * (2 * m + r).choose (m + j)) *
        (((j : ℝ) + 1) * (m + r - j : ℕ)) := by
      nlinarith [congrArg (fun x : ℝ => r.choose j * ((j : ℝ) + 1) * x) hden]
    _ ≤ ((r.choose j : ℝ) * (2 * m + r).choose (m + j)) *
        (((r - j : ℕ) : ℝ) * ((m : ℝ) + j + 1)) :=
      mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = _ := by
      nlinarith [congrArg
        (fun x : ℝ => (2 * m + r).choose (m + j) * ((m : ℝ) + j + 1) * x) hnum]

/-- The coefficient ratio is maximal at the middle of the padding row. -/
theorem chooseRatio_le_middle (m r j : ℕ) (hj : j ≤ r) :
    chooseRatio m r j ≤ chooseRatio m r (r / 2) := by
  have hleft (k : ℕ) (hk : k ≤ r / 2) : chooseRatio m r k ≤ chooseRatio m r (r / 2) := by
    refine Nat.decreasingInduction ?_ ?_ hk
    · intro k hk IH
      exact (chooseRatio_step m r k (by omega)).trans IH
    · exact le_rfl
  by_cases hmiddle : j ≤ r / 2
  · exact hleft j hmiddle
  · rw [← chooseRatio_symm m r j hj]
    exact hleft (r - j) (by omega)

private theorem chooseRatio_middle (m r : ℕ) :
    chooseRatio m r (r / 2) = (middle r : ℝ) / middle (2 * m + r) := by
  simp only [chooseRatio, middle, show (2 * m + r) / 2 = m + r / 2 by omega]

/-- Every integer acceptance numerator is at most its positive denominator. -/
theorem choose_acceptance_bound (m r j : ℕ) (hr : 0 < r) (hpadding : 2 * m ≤ 3 * r)
    (hj : j ≤ r) : 4 ^ m * r.choose j ≤ 2 * (2 * m + r).choose (m + j) := by
  have hmid : (0 : ℝ) < (middle (2 * m + r) : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.div_le_self (2 * m + r) 2)
  have hc := central_acceptance_bound m r hr hpadding
  rw [Nat.add_comm r (2 * m)] at hc
  have hratio := chooseRatio_le_middle m r j hj
  rw [chooseRatio_middle, chooseRatio] at hratio
  have hcross := (div_le_div_iff₀ (denominator_pos m r j hj) hmid).mp hratio
  have hbound : (4 : ℝ) ^ m * r.choose j ≤ 2 * (2 * m + r).choose (m + j) := by
    apply (mul_le_mul_iff_right₀ hmid).mp
    calc
      _ = (4 : ℝ) ^ m * ((r.choose j : ℝ) * middle (2 * m + r)) := by ring
      _ ≤ (4 : ℝ) ^ m * ((middle r : ℝ) * (2 * m + r).choose (m + j)) :=
        mul_le_mul_of_nonneg_left hcross (by positivity)
      _ = ((4 : ℝ) ^ m * middle r) * (2 * m + r).choose (m + j) := by ring
      _ ≤ (2 * (middle (2 * m + r) : ℝ)) * (2 * m + r).choose (m + j) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  exact_mod_cast hbound

theorem acceptance_mem (m r j : ℕ) (hr : 0 < r) (hpadding : 2 * m ≤ 3 * r) :
    0 ≤ acceptance m r j ∧ acceptance m r j ≤ 1 := by
  by_cases hband : m ≤ j ∧ j ≤ m + r
  · have hden : (0 : ℝ) < (2 * m + r).choose j := by
      exact_mod_cast Nat.choose_pos (by omega : j ≤ 2 * m + r)
    have hnum := choose_acceptance_bound m r (j - m) hr hpadding (by omega)
    rw [show m + (j - m) = j by omega] at hnum
    rw [acceptance, ite_eq_left hband]
    exact ⟨by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hnum)⟩
  · simp only [acceptance, ite_eq_right hband, le_rfl, zero_le_one, and_self]

/-- The exact padding used by the source; its strict excess makes all ratios admissible. -/
def padding (m : ℕ) : ℕ := 2 * m / 3 + 1

theorem padding_pos (m : ℕ) : 0 < padding m := Nat.succ_pos _
theorem padding_large (m : ℕ) : 2 * m ≤ 3 * padding m := by unfold padding; omega

def acceptanceBias (m j : ℕ) : unitInterval :=
  ⟨acceptance m (padding m) j, acceptance_mem m (padding m) j (padding_pos m) (padding_large m)⟩

end

end SampLib.MinimumComplement
