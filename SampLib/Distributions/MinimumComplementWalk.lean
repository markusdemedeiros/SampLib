module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! # Harmonic credits for the fair first-passage walk

The smaller quadratic root `h` satisfies `2h=t(1+h²)`. Thus
`t^(steps+1)h^pending/2` is unchanged in expectation by a fair step. At absorption
it is the conditional binomial success probability; initially it is `min(p,1-p)`.
-/

namespace SampLib.MinimumComplement.Walk

noncomputable section

def root (t : unitInterval) : ℝ := Real.sqrt (1 - (t : ℝ) ^ 2)

theorem root_square (t : unitInterval) : root t ^ 2 = 1 - (t : ℝ) ^ 2 :=
  Real.sq_sqrt (by nlinarith [t.2.1, t.2.2])

theorem root_mem (t : unitInterval) : 0 ≤ root t ∧ root t ≤ 1 := by
  have hs := root_square t
  exact ⟨Real.sqrt_nonneg _, by nlinarith [Real.sqrt_nonneg (1 - (t : ℝ) ^ 2)]⟩

/-- The smaller quadratic root, with its total value zero at `t=0`. -/
def tilt (t : unitInterval) : unitInterval :=
  ⟨(1 - root t) / t, div_nonneg (sub_nonneg.mpr (root_mem t).2) t.2.1, by
    by_cases ht : (t : ℝ) = 0
    · simp [ht]
    · apply (div_le_one (lt_of_le_of_ne t.2.1 (Ne.symm ht))).mpr
      have hs := root_square t
      have hu := (root_mem t).1
      nlinarith [mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2)]⟩

/-- The division-free identity also holds at the zero endpoint. -/
theorem quadratic (t : unitInterval) :
    2 * (tilt t : ℝ) = (t : ℝ) * (1 + (tilt t : ℝ) ^ 2) := by
  by_cases ht : (t : ℝ) = 0
  · simp [tilt, ht]
  · have hs := root_square t
    dsimp [tilt]
    field_simp
    nlinarith

theorem mul_tilt (t : unitInterval) :
    (t : ℝ) * (tilt t : ℝ) = 1 - root t := by
  by_cases ht : (t : ℝ) = 0
  · simp [tilt, root, ht]
  · simp only [tilt]
    field_simp

/-- Probability credit at `pending=k` after `steps=s` fair flips. -/
def coefficient (t : unitInterval) (k s : ℕ) : ℝ :=
  (t : ℝ) ^ (s + 1) * (tilt t : ℝ) ^ k / 2

theorem coefficient_mem (t : unitInterval) (k s : ℕ) :
    0 ≤ coefficient t k s ∧ coefficient t k s ≤ 1 := by
  have ht := pow_le_one₀ t.2.1 t.2.2 (n := s + 1)
  have hh := pow_le_one₀ (tilt t).2.1 (tilt t).2.2 (n := k)
  have hp : (t : ℝ) ^ (s + 1) * (tilt t : ℝ) ^ k ≤ 1 :=
    (mul_le_mul_of_nonneg_right ht (pow_nonneg (tilt t).2.1 _)).trans
      (by simpa only [one_mul] using hh)
  constructor
  · exact div_nonneg (mul_nonneg (pow_nonneg t.2.1 _) (pow_nonneg (tilt t).2.1 _))
      (by norm_num)
  · unfold coefficient
    nlinarith

def bias (t : unitInterval) (k s : ℕ) : unitInterval :=
  ⟨coefficient t k s, coefficient_mem t k s⟩

/-- One fair step either removes or adds a pending level and advances the clock. -/
theorem harmonic (t : unitInterval) (k s : ℕ) :
    (coefficient t k (s + 1) + coefficient t (k + 2) (s + 1)) / 2 =
      coefficient t (k + 1) s := by
  have h := congrArg (fun x : ℝ => (t : ℝ) ^ (s + 1) * (tilt t : ℝ) ^ k * x / 4)
    (quadratic t)
  simp only [coefficient, pow_succ] at h ⊢
  nlinarith [h]

/-- The square root parameter for an input coin of bias `p`. -/
def parameter (p : unitInterval) : unitInterval :=
  ⟨2 * Real.sqrt ((p : ℝ) * (1 - p)), by positivity, by
    have hz : 0 ≤ (p : ℝ) * (1 - p) := mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2)
    have hs := Real.sq_sqrt hz
    have hu := Real.sqrt_nonneg ((p : ℝ) * (1 - p))
    nlinarith [sq_nonneg (2 * (p : ℝ) - 1)]⟩

theorem parameter_square (p : unitInterval) :
    (parameter p : ℝ) ^ 2 = 4 * p * (1 - p) := by
  have hs := Real.sq_sqrt (mul_nonneg p.2.1 (sub_nonneg.mpr p.2.2))
  dsimp [parameter]
  nlinarith

/-- At the initial pending level, the smaller root is exactly the smaller input mass. -/
theorem initial (p : unitInterval) :
    coefficient (parameter p) 1 0 = min (p : ℝ) (1 - p) := by
  simp only [coefficient, Nat.zero_add, pow_one]
  rw [mul_tilt]
  simp only [root, parameter_square]
  rw [show 1 - 4 * (p : ℝ) * (1 - p) = (2 * (p : ℝ) - 1) ^ 2 by ring,
    Real.sqrt_sq_eq_abs]
  by_cases hp : (p : ℝ) ≤ 1 / 2
  · rw [abs_of_nonpos (by linarith), min_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]
    ring

/-- Absorption after `2m-1` flips matches the exact binomial-stage probability. -/
theorem absorbed (p : unitInterval) (m : ℕ) (hm : 0 < m) :
    coefficient (parameter p) 0 (2 * m - 1) = (4 * p * (1 - p)) ^ m / 2 := by
  simp only [coefficient, pow_zero, mul_one]
  rw [show 2 * m - 1 + 1 = 2 * m by omega, pow_mul, parameter_square]

end

end SampLib.MinimumComplement.Walk
