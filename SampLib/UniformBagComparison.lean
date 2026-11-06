import SampLib.UniformBag

/-! # Comparison kernels for cached uniform bags -/

open scoped ENNReal

namespace SampLib.UniformBag

noncomputable section

/-- Threshold seen in the tail after fixing the head digit. -/
def tailNumerator (x y : ℤ) (b : Bool) : ℤ := 2 * x - if b then y else 0

theorem tailThreshold (x y : ℤ) (b : Bool) (hy : 0 < y) :
    (tailNumerator x y b : ℝ) / y =
      2 * ((x : ℝ) / y) - if b then 1 else 0 := by
  have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  cases b <;> simp only [tailNumerator, Bool.false_eq_true, ite_false, ite_true,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat, sub_zero] <;>
    field_simp

/-- A resolved tail comparison is the desired comparison on the whole bag. -/
theorem resolves_tail (p : List Bool) (x y : ℤ) (b result : Bool) (hy : 0 < y)
    (h : DyadicPosterior.resolves p ((tailNumerator x y b : ℝ) / y) result) :
    DyadicPosterior.resolves (b :: p) ((x : ℝ) / y) result := by
  rw [DyadicPosterior.resolves_cons, ← tailThreshold x y b hy]
  exact h

/-- A returned bit is determined by the updated cache's posterior. -/
def comparisonResult (p : List Bool) (x y : ℤ) (result : Bool) (q : List Bool) : Prop :=
  p <+: q ∧ DyadicPosterior.resolves q ((x : ℝ) / y) result

theorem comparisonResult_tail {p q r : List Bool} {x y : ℤ} {b result : Bool}
    (hs : stepRefines p b q) (hy : 0 < y)
    (hr : comparisonResult q (tailNumerator x y b) y result r) :
    comparisonResult p x y result (b :: r) := by
  refine ⟨?_, resolves_tail r x y b result hy hr.2⟩
  rcases hs with ⟨rfl, _⟩ | rfl
  · exact List.nil_prefix
  · exact List.cons_prefix_cons.mpr ⟨rfl, hr.1⟩

/-- Exactly one fresh head can require another comparison step. -/
def retryBit (x y : ℤ) : Bool := decide (y ≤ 2 * x)

theorem resolves_nonpos (p : List Bool) (x y : ℤ) (hx : x ≤ 0) (hy : 0 < y) :
    DyadicPosterior.resolves p ((x : ℝ) / y) false := by
  apply DyadicPosterior.resolves_false
  exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hx) (by exact_mod_cast hy.le)

theorem resolves_ge (p : List Bool) (x y : ℤ) (hx : y ≤ x) (hy : 0 < y) :
    DyadicPosterior.resolves p ((x : ℝ) / y) true := by
  apply DyadicPosterior.resolves_true
  exact (le_div_iff₀ (by exact_mod_cast hy : (0 : ℝ) < y)).mpr (by
    simpa using (show (y : ℝ) ≤ x by exact_mod_cast hx))

/-- The noncontinuing child decides the comparison independently of its tail. -/
theorem exit_resolves (p : List Bool) (x y : ℤ) (hy : 0 < y) (b : Bool)
    (hb : b ≠ retryBit x y) :
    DyadicPosterior.resolves (b :: p) ((x : ℝ) / y) (!b) := by
  apply resolves_tail p x y b (!b) hy
  cases b with
  | false =>
    have hxy : y ≤ 2 * x := by simpa [retryBit] using hb
    apply resolves_ge p _ y _ hy
    simpa [tailNumerator] using hxy
  | true =>
    have hxy : 2 * x < y := by simpa [retryBit, not_le] using hb
    apply resolves_nonpos p _ y _ hy
    simp only [tailNumerator, ite_true]
    omega

/-- The continuing child receives twice the auxiliary termination credit. -/
def comparisonCredit (F : ℝ → ℝ≥0∞) (retry : Bool) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  DyadicPosterior.credit [b] F + if b = retry then 2 * ε else 0

/-- Fresh refinement preserves posterior credit; its sole retry consumes one ε on average. -/
theorem comparison_expectation (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (retry : Bool) (ε : ℝ≥0∞) :
    (∫⁻ b, comparisonCredit F retry ε b ∂RealCoin.law VonNeumann.fairBias) =
      DyadicPosterior.credit [] F + ε := by
  have hsplit := DyadicPosterior.credit_split [] F hF
  simp only [List.nil_append] at hsplit
  rw [hsplit, RealCoin.lintegral_law]
  cases retry <;>
    norm_num [comparisonCredit, RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias]
  all_goals
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    calc
      _ = (DyadicPosterior.credit [false] F + DyadicPosterior.credit [true] F) / 2 +
          ((2 : ℝ≥0∞)⁻¹ * 2) * ε := by
        simp only [ENNReal.div_eq_inv_mul]
        ring
      _ = _ := by
        rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]

end

end SampLib.UniformBag
