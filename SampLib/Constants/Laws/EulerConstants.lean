import SampLib.Bernoulli.Laws.EulerNumberBounds
import SampLib.Bernoulli.Laws.RealEnclosure
import SampLib.Bernoulli.Laws.RealEnclosureTransforms

/-! # Affine and fractional-linear constants from factorial enclosures -/

namespace SampLib.EulerConstants

noncomputable section

abbrev minusTwo : unitInterval :=
  ⟨Real.exp 1 - 2, by linarith [EulerNumber.exp_one_gt_two],
    by linarith [EulerNumber.exp_one_lt_three]⟩

abbrev threeMinus : unitInterval :=
  ⟨3 - Real.exp 1, by linarith [EulerNumber.exp_one_lt_three],
    by linarith [EulerNumber.exp_one_gt_two]⟩

def minusTwoInterval (n : ℕ) : FromBounds.Interval minusTwo :=
  ((EulerEnclosure.interval n).affine 2 1 (by decide)).toProbability _ (by simp)

theorem minusTwo_tight : FromBounds.Tight minusTwoInterval :=
  (EulerEnclosure.tight.affine 2 1 (by decide)).toProbability _ (by simp)

private def reflected (n : ℕ) : RealEnclosure.Interval (3 - Real.exp 1) where
  lower := 3 * (EulerEnclosure.interval n).denominator - (EulerEnclosure.interval n).upper
  upper := 3 * (EulerEnclosure.interval n).denominator - (EulerEnclosure.interval n).lower
  denominator := (EulerEnclosure.interval n).denominator
  positive := (EulerEnclosure.interval n).positive
  below := by
    push_cast
    nlinarith [(EulerEnclosure.interval n).above]
  above := by
    push_cast
    nlinarith [(EulerEnclosure.interval n).below]

def threeMinusInterval (n : ℕ) : FromBounds.Interval threeMinus :=
  (reflected n).toProbability _ rfl

private theorem reflected_width (n : ℕ) :
    (reflected n).width = (EulerEnclosure.interval n).width := by
  dsimp [RealEnclosure.Interval.width, RealEnclosure.Interval.left,
    RealEnclosure.Interval.right, reflected]
  push_cast
  ring

theorem threeMinus_tight : FromBounds.Tight threeMinusInterval := by
  apply RealEnclosure.Tight.toProbability _ _ rfl
  intro ε hε
  obtain ⟨n, hn⟩ := EulerEnclosure.tight ε hε
  exact ⟨n, by simpa only [reflected_width] using hn⟩

end

end SampLib.EulerConstants
