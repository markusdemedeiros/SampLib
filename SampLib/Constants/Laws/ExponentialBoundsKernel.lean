import SampLib.Bernoulli.Laws.RealEnclosure
import SampLib.Constants.Laws.ExponentialEnclosure

/-! # The concrete integer Taylor intervals used by `expMinusBounds` -/

namespace SampLib.ExponentialEnclosure

noncomputable section

def power (x k : ℕ) : ℤ := (-(x : ℤ)) ^ (k + 1)

def middle (x y k : ℕ) : ℤ := numerator x y k * (y * (k + 1))

def lower (x y k : ℕ) : ℤ :=
  if power x k < 0 then middle x y k + power x k else middle x y k

def upper (x y k : ℕ) : ℤ :=
  if power x k < 0 then middle x y k else middle x y k + power x k

theorem middle_ratio (x y k : ℕ) (hy : 0 < y) :
    (middle x y k : ℝ) / denominator y (k + 1) = partialSum ((x : ℝ) / y) k := by
  rw [← numerator_ratio x y k hy]
  simp only [middle, denominator, Nat.factorial_succ, pow_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Int.cast_mul, Int.cast_natCast, Int.cast_add, Int.cast_one]
  have hy' : (y : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hkp : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem power_ratio (x y k : ℕ) :
    (power x k : ℝ) / denominator y (k + 1) =
      (-((x : ℝ) / y)) ^ (k + 1) / (k + 1).factorial := by
  simp only [power, denominator, Int.cast_pow, Int.cast_neg, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_pow]
  rw [← neg_div, div_pow]
  ring

private theorem scaled_remainder (x y k : ℕ) (hy : 0 < y) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      Real.exp (-((x : ℝ) / y)) * denominator y (k + 1) =
        middle x y k + θ * power x k := by
  obtain ⟨θ, hθ, heq⟩ := remainder ((x : ℝ) / y) (by positivity) k
  refine ⟨θ, hθ, ?_⟩
  rw [← middle_ratio x y k hy, ← power_ratio x y k] at heq
  have hd : (denominator y (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (denominator_positive y (k + 1) hy).ne'
  field_simp at heq
  nlinarith [heq]

/-- The neighboring partial sums enclose the target exponential. -/
theorem bounds (x y k : ℕ) (hy : 0 < y) :
    (lower x y k : ℝ) ≤ Real.exp (-((x : ℝ) / y)) * denominator y (k + 1) ∧
      Real.exp (-((x : ℝ) / y)) * denominator y (k + 1) ≤ upper x y k := by
  obtain ⟨θ, hθ, heq⟩ := scaled_remainder x y k hy
  by_cases hδ : power x k < 0
  · have hδ' : (power x k : ℝ) ≤ 0 := by exact_mod_cast hδ.le
    have hlo := mul_le_mul_of_nonpos_right hθ.2 hδ'
    have hhi := mul_nonpos_of_nonneg_of_nonpos hθ.1 hδ'
    simp only [lower, upper, ite_eq_left hδ, Int.cast_add]
    constructor <;> nlinarith
  · have hδ' : (0 : ℝ) ≤ power x k := by exact_mod_cast not_lt.mp hδ
    have hlo := mul_nonneg hθ.1 hδ'
    have hhi := mul_le_mul_of_nonneg_right hθ.2 hδ'
    simp only [lower, upper, ite_eq_right hδ, Int.cast_add]
    constructor <;> nlinarith

/-- The actual source's truncation index; the validity argument needs no cutoff restriction. -/
def last (x y n : ℕ) : ℕ := x / y + 2 * n + 1

def interval (x y : ℕ) (hy : 0 < y) (n : ℕ) :
    RealEnclosure.Interval (Real.exp (-((x : ℝ) / y))) where
  lower := lower x y (last x y n)
  upper := upper x y (last x y n)
  denominator := denominator y (last x y n + 1)
  positive := denominator_positive y _ hy
  below := (bounds x y _ hy).1
  above := (bounds x y _ hy).2

theorem gap (x y k : ℕ) : upper x y k - lower x y k = |power x k| := by
  unfold lower upper
  split_ifs with h
  · rw [abs_of_neg h]
    omega
  · rw [abs_of_nonneg (not_lt.mp h)]
    omega

@[simp] theorem width (x y : ℕ) (hy : 0 < y) (n : ℕ) :
    (interval x y hy n).width =
      ((x : ℝ) / y) ^ (last x y n + 1) / (last x y n + 1).factorial := by
  simp only [RealEnclosure.Interval.width, RealEnclosure.Interval.left,
    RealEnclosure.Interval.right, interval]
  rw [← sub_div, ← Int.cast_sub, gap]
  simp only [power, denominator, Int.cast_pow,
    Int.cast_natCast, abs_pow, abs_neg, Nat.abs_cast, Nat.cast_mul, Nat.cast_pow]
  rw [div_pow]
  ring

theorem width_tendsto (x y : ℕ) (hy : 0 < y) :
    Filter.Tendsto (fun n => (interval x y hy n).width) Filter.atTop (nhds 0) := by
  simp only [width]
  apply (Real.summable_pow_div_factorial ((x : ℝ) / y)).tendsto_atTop_zero.comp
  apply Filter.tendsto_atTop_mono (f := fun n : ℕ => n) _ Filter.tendsto_id
  intro n
  change n ≤ x / y + 2 * n + 1 + 1
  calc
    n ≤ x / y + n + n := Nat.le_add_left n _
    _ ≤ x / y + 2 * n + 1 + 1 := by omega

theorem tight (x y : ℕ) (hy : 0 < y) : RealEnclosure.Tight (interval x y hy) :=
  RealEnclosure.Tight.of_tendsto _ (width_tendsto x y hy)

end

end SampLib.ExponentialEnclosure
