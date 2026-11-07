module

public import SampLib.Constants.Laws.RealContinuedFractionBudget

@[expose] public section

/-! # Positive integer continued fractions

An integer coefficient is a real coefficient with integer entries. Its prefixes and value
agree with those of `RealContinuedFraction`, so every bound transfers from there.
-/

open Set
open scoped NNReal

namespace SampLib.ContinuedFraction

noncomputable section

/-- A positive numerator no larger than its positive denominator. -/
structure Coefficient where
  numerator : ℕ
  denominator : ℕ
  positive : 0 < numerator
  bounded : numerator ≤ denominator
  last : Bool

theorem Coefficient.denominator_pos (c : Coefficient) : 0 < c.denominator :=
  c.positive.trans_le c.bounded

/-- The same coefficient read over the reals. -/
def Coefficient.real (c : Coefficient) : RealContinuedFraction.Coefficient where
  numerator := c.numerator
  denominator := c.denominator
  positive := by exact_mod_cast c.positive
  lower := by exact_mod_cast c.denominator_pos
  bounded := by exact_mod_cast c.bounded
  last := c.last

/-- The coefficient sequence read over the reals. -/
abbrev sequence (a : ℕ → Coefficient) := fun i => (a i).real

def tailInput (c : Coefficient) (x : unitInterval) : unitInterval :=
  if c.last then 0 else x

/-- One coefficient acts by `b/(a+x)`; a final coefficient ignores the tail. -/
def step (c : Coefficient) (x : unitInterval) : unitInterval :=
  ⟨(c.numerator : ℝ) / (c.denominator + (tailInput c x : ℝ)),
    div_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _) (tailInput c x).2.1), by
      have ha : (0 : ℝ) < c.denominator := by exact_mod_cast c.denominator_pos
      have hb : (c.numerator : ℝ) ≤ c.denominator := by exact_mod_cast c.bounded
      apply (div_le_one (add_pos_of_pos_of_nonneg ha (tailInput c x).2.1)).mpr
      exact hb.trans (le_add_of_nonneg_right (tailInput c x).2.1)⟩

/-- Apply the first `n` coefficients to an arbitrary terminal tail. -/
def expand (a : ℕ → Coefficient) (i : ℕ) : ℕ → unitInterval → unitInterval
  | 0, x => x
  | n + 1, x => step (a i) (expand a (i + 1) n x)

theorem step_eq (c : Coefficient) : step c = RealContinuedFraction.step c.real := rfl

theorem expand_eq (a : ℕ → Coefficient) (i n : ℕ) :
    expand a i n = RealContinuedFraction.expand (sequence a) i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n IH =>
    funext x
    simp only [expand, RealContinuedFraction.expand, IH, step_eq]

/-- A continued fraction has at least one value compatible with every finite prefix. -/
theorem exists_value (a : ℕ → Coefficient) (i : ℕ) :
    (⋂ n : ℕ, range (expand a i n)).Nonempty := by
  simpa only [expand_eq] using RealContinuedFraction.exists_value (sequence a) i

/-- No two values can remain in every finite-prefix interval. -/
theorem unique_value (a : ℕ → Coefficient) (i : ℕ) (x y : unitInterval)
    (hx : ∀ n, x ∈ range (expand a i n)) (hy : ∀ n, y ∈ range (expand a i n)) :
    x = y :=
  RealContinuedFraction.unique_value (sequence a) i x y
    (fun n => by simpa only [expand_eq] using hx n) (fun n => by simpa only [expand_eq] using hy n)

/-- The real value enclosed by all finite continued-fraction prefixes. -/
def value (a : ℕ → Coefficient) (i : ℕ) : unitInterval :=
  Classical.choose (exists_value a i)

theorem value_mem (a : ℕ → Coefficient) (i n : ℕ) :
    value a i ∈ range (expand a i n) :=
  mem_iInter.mp (Classical.choose_spec (exists_value a i)) n

/-- The integer fraction is the real fraction of its embedded coefficients. -/
theorem value_eq (a : ℕ → Coefficient) (i : ℕ) :
    value a i = RealContinuedFraction.value (sequence a) i :=
  RealContinuedFraction.unique_value (sequence a) i _ _
    (fun n => by simpa only [expand_eq] using value_mem a i n) (RealContinuedFraction.value_mem _ i)

/-- A final flag makes the fraction independent of every later coefficient. -/
theorem value_coe (a : ℕ → Coefficient) (i : ℕ) :
    (value a i : ℝ) = (a i).numerator /
      ((a i).denominator + if (a i).last then 0 else (value a (i + 1) : ℝ)) := by
  rw [value_eq, value_eq]
  exact RealContinuedFraction.value_coe (sequence a) i

/-- The branching recursion pays between one and two units at each position. -/
def potential (c : Coefficient) : ℝ≥0 :=
  ⟨1 + 1 / (c.denominator : ℝ), by positivity⟩

theorem one_le_potential (c : Coefficient) : 1 ≤ potential c :=
  RealContinuedFraction.one_le_potential c.real

theorem potential_le_two (c : Coefficient) : potential c ≤ 2 :=
  RealContinuedFraction.potential_le_two c.real

/-- Both recursive calls fit in three quarters of the current potential. -/
theorem recursive_budget (a : ℕ → Coefficient) (i : ℕ) :
    (1 / ((a i).denominator + 1 : ℝ)) *
        ((potential (a (i + 1)) : ℝ) +
          (1 - (value a (i + 1) : ℝ)) * (potential (a i) : ℝ)) ≤
      (3 / 4 : ℝ) * (potential (a i) : ℝ) := by
  rw [value_eq]
  exact RealContinuedFraction.recursive_budget (sequence a) i
    (show (1 : ℝ) ≤ (a (i + 1)).numerator from Nat.one_le_cast.mpr (a (i + 1)).positive)

end

end SampLib.ContinuedFraction
