import SampLib.PSRN.Support.Represented.Uniform
import SampLib.PSRN.Support.Represented.IntegerPower
import SampLib.PSRN.Support.Represented.Reciprocal
import SampLib.PSRN.Support.Root.Latent

/-! # The model of a rational power of one deferred uniform

The model has three branches: a constant for a zero exponent, a power with an optional
root for a positive exponent, and the reciprocal of that root for a negative exponent.
Every branch views the same uniform world, and the uniform is positive almost surely.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNPowerUniform

noncomputable section

open LatentReal

abbrev U := LatentUniform.model

/-- A lazy real over the uniform world, bundled with its exact interval schedule. -/
abbrev Stage := (D : Model ℝ (List Bool)) × Representation D

def power (a : ℕ) : Stage :=
  ⟨IntegerPower.model U a, IntegerPower.representation U LatentUniform.representation a⟩

/-- The source returns the power itself for degree one and a bisection root otherwise. -/
def rooted (a b : ℕ) : Stage :=
  if b = 1 then power a
  else ⟨(power a).1.nthRoot b, ((power a).1.nthRoot b).dyadicRepresentation⟩

def reciprocal (X : Stage) : Stage :=
  ⟨RepresentedReciprocal.model X.1 X.2, RepresentedReciprocal.representation X.1 X.2⟩

/-- The three branches of `powerRational`, selected by the sign of the numerator. -/
def stage (a : ℤ) (b : ℕ) : Stage :=
  if a = 0 then ⟨U.constant 1, Representation.point U 1 1 1 (by decide) (by norm_num)⟩
  else if 0 < a then rooted a.natAbs b
  else reciprocal (rooted a.natAbs b)

abbrev model (a : ℤ) (b : ℕ) : Model ℝ (List Bool) := (stage a b).1

abbrev representation (a : ℤ) (b : ℕ) : Representation (model a b) := (stage a b).2

theorem stage_zero (b : ℕ) :
    stage 0 b = ⟨U.constant 1, Representation.point U 1 1 1 (by decide) (by norm_num)⟩ := by
  simp [stage]

theorem stage_pos {a : ℤ} (b : ℕ) (ha : 0 < a) : stage a b = rooted a.natAbs b := by
  simp [stage, ha.ne', ha]

theorem stage_neg {a : ℤ} (b : ℕ) (ha : a < 0) :
    stage a b = reciprocal (rooted a.natAbs b) := by
  simp [stage, ha.ne, not_lt.mpr ha.le]

theorem rooted_one (a : ℕ) : rooted a 1 = power a := by simp [rooted]

theorem rooted_root (a : ℕ) {b : ℕ} (hb : b ≠ 1) :
    rooted a b = ⟨(power a).1.nthRoot b, ((power a).1.nthRoot b).dyadicRepresentation⟩ := by
  simp [rooted, hb]

section world

theorem power_sameWorld (a : ℕ) : U.SameWorld (power a).1 := IntegerPower.sameWorld U a

theorem rooted_sameWorld (a b : ℕ) : U.SameWorld (rooted a b).1 := by
  unfold rooted
  split
  · exact power_sameWorld a
  · exact (power_sameWorld a).trans ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

theorem sameWorld (a : ℤ) (b : ℕ) : U.SameWorld (model a b) := by
  unfold model stage
  split
  · exact U.sameWorld_constant 1
  split
  · exact rooted_sameWorld _ _
  · exact (rooted_sameWorld _ _).trans (RepresentedReciprocal.sameWorld _ _)

end world

section mathematics

open MeasureTheory

/-- Every uniform posterior is concentrated on positive reals. -/
theorem ae_pos (p : List Bool) : ∀ᵐ u ∂DyadicPosterior.law p, 0 < u := by
  have hne := (DyadicPosterior.law []).ae_ne 0
  rw [DyadicPosterior.law_nil] at hne
  have hunit : ∀ᵐ u ∂DyadicPosterior.unitLaw, 0 < u := by
    filter_upwards [ae_restrict_mem measurableSet_Ico, hne] with u hu h0
    exact lt_of_le_of_ne hu.1 (Ne.symm h0)
  exact DyadicPosterior.law_absolutelyContinuous_unit p |>.ae_le hunit

theorem power_value (a : ℕ) (u : ℝ) : (power a).1.value u = u ^ a :=
  IntegerPower.value_eq U a u

theorem rooted_value (a b : ℕ) (hb : 0 < b) {u : ℝ} (hu : 0 ≤ u) :
    (rooted a b).1.value u = u ^ ((a : ℝ) / b) := by
  unfold rooted
  split
  · subst b
    simp [power_value]
  · change root b ((power a).1.value u) = _
    rw [power_value, root, ← Real.rpow_natCast, ← Real.rpow_mul hu, div_eq_mul_inv]

/-- On the positive half-line every branch computes the real power `u ^ (a / b)`. -/
theorem model_value (a : ℤ) {b : ℕ} (hb : 0 < b) {u : ℝ} (hu : 0 < u) :
    (model a b).value u = u ^ ((a : ℝ) / b) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [model, stage_neg b ha]
    change 1 / (rooted a.natAbs b).1.value u = _
    rw [rooted_value _ _ hb hu.le, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast ha),
      one_div, ← Real.rpow_neg hu.le, neg_div, neg_neg]
  · simp [model, stage_zero, Model.constant]
  · rw [model, stage_pos b ha, rooted_value _ _ hb hu.le, Nat.cast_natAbs, Int.cast_abs,
      abs_of_pos (by exact_mod_cast ha)]

/-- The output law is the image of the unit uniform under `u ↦ u ^ (a / b)`. -/
theorem initial_law (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (model a b).law [] = DyadicPosterior.unitLaw.map (fun u => u ^ ((a : ℝ) / b)) := by
  rw [Model.law, (sameWorld a b).posterior_eq]
  change (DyadicPosterior.law []).map _ = _
  rw [DyadicPosterior.law_nil]
  apply Measure.map_congr
  have hpos := ae_pos []
  rw [DyadicPosterior.law_nil] at hpos
  filter_upwards [hpos] with u hu
  exact model_value a hb hu

/-- The power avoids every rational root threshold, so the bisection terminates. -/
theorem admissible (a b : ℕ) (ha : 0 < a) (p : List Bool) :
    Root.Admissible (power a).1 b p := by
  rw [Root.Admissible, (power_sameWorld a).posterior_eq]
  refine ⟨?_, fun c d _ _ => ?_⟩
  · filter_upwards [ae_pos p] with u hu
    rw [power_value]
    positivity
  · filter_upwards [ae_pos p, (DyadicPosterior.law p).ae_ne ((((c : ℝ) / d) ^ b) ^ (a⁻¹ : ℝ))]
      with u hu hne heq
    rw [power_value] at heq
    exact hne (by rw [← heq, Real.pow_rpow_inv_natCast hu.le ha.ne'])

/-- Every posterior keeps the reciprocal's denominator away from zero. -/
theorem rooted_nonzero (a b : ℕ) (hb : 0 < b) (p : List Bool) :
    ∀ᵐ u ∂(rooted a b).1.posterior p, (rooted a b).1.value u ≠ 0 := by
  rw [(rooted_sameWorld a b).posterior_eq]
  filter_upwards [ae_pos p] with u hu
  rw [rooted_value a b hb hu.le]
  exact (Real.rpow_pos_of_pos hu _).ne'

/-- No branch vanishes, so the actual reciprocal of any power uniform terminates. -/
theorem model_nonzero (a : ℤ) {b : ℕ} (hb : 0 < b) (p : List Bool) :
    ∀ᵐ u ∂(model a b).posterior p, (model a b).value u ≠ 0 := by
  rw [(sameWorld a b).posterior_eq]
  filter_upwards [ae_pos p] with u hu
  rw [model_value a hb hu]
  exact (Real.rpow_pos_of_pos hu _).ne'

end mathematics

end

end SampLib.PSRNPowerUniform
