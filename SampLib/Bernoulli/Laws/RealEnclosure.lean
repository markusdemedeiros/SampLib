import SampLib.Common.Laws.BoundsKernel
import SampLib.Constants.FromBounds
import SampLib.Bernoulli.Laws.AlternatingEnclosure

/-! # Rational enclosures of arbitrary real constants -/

open Filter
open scoped Topology

namespace SampLib.RealEnclosure

noncomputable section

/-- Integer endpoints share one positive denominator. -/
structure Interval (x : ℝ) where
  lower : ℤ
  upper : ℤ
  denominator : ℕ
  positive : 0 < denominator
  below : (lower : ℝ) ≤ x * denominator
  above : x * denominator ≤ upper

def Interval.left {x : ℝ} (a : Interval x) : ℝ := a.lower / (a.denominator : ℝ)

def Interval.right {x : ℝ} (a : Interval x) : ℝ := a.upper / (a.denominator : ℝ)

def Interval.width {x : ℝ} (a : Interval x) : ℝ := a.right - a.left

theorem Interval.left_le {x : ℝ} (a : Interval x) : a.left ≤ x :=
  (div_le_iff₀ (by exact_mod_cast a.positive)).mpr a.below

theorem Interval.le_right {x : ℝ} (a : Interval x) : x ≤ a.right :=
  (le_div_iff₀ (by exact_mod_cast a.positive)).mpr a.above

theorem Interval.width_nonneg {x : ℝ} (a : Interval x) : 0 ≤ a.width :=
  sub_nonneg.mpr (a.left_le.trans a.le_right)

/-- Arbitrarily small widths provide the finite horizon needed by the sampling engine. -/
def Tight {x : ℝ} (a : ℕ → Interval x) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n, (a n).width ≤ ε

theorem Tight.of_tendsto {x : ℝ} (a : ℕ → Interval x)
    (h : Tendsto (fun n => (a n).width) atTop (𝓝 0)) : Tight a := by
  intro ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp h).2 ε hε).exists
  exact ⟨n, hn.le⟩

/-- Restrict a real enclosure to a target known to be a probability. -/
def Interval.toProbability {x : ℝ} (a : Interval x) (p : unitInterval)
    (hx : (p : ℝ) = x) : FromBounds.Interval p where
  lower := a.lower
  upper := a.upper
  denominator := a.denominator
  positive := a.positive
  below := by simpa only [hx] using a.below
  above := by simpa only [hx] using a.above

theorem Tight.toProbability {x : ℝ} {a : ℕ → Interval x} (h : Tight a)
    (p : unitInterval) (hx : (p : ℝ) = x) :
    FromBounds.Tight (fun n => (a n).toProbability p hx) := h

/-- Concrete gateways return an all-integer `(lower,(upper,denominator))` triple. -/
def encodeTriple {rT : Type} (a : ℤ × (ℤ × ℤ)) : ProbLang.Val rT :=
  .pair (.int a.1) (.pair (.int a.2.1) (.int a.2.2))

def Interval.triple {x : ℝ} (a : Interval x) : ℤ × (ℤ × ℤ) :=
  (a.lower, (a.upper, (a.denominator : ℤ)))

def encodeInterval {rT : Type} {x : ℝ} (a : Interval x) : ProbLang.Val rT :=
  encodeTriple a.triple

@[simp] theorem encode_toProbability {rT : Type} {x : ℝ} (a : Interval x)
    (p : unitInterval) (hx : (p : ℝ) = x) :
    FromBounds.encodeInterval (rT := rT) (a.toProbability p hx) = encodeInterval a := rfl

end

end SampLib.RealEnclosure
