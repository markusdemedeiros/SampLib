import SampLib.Distributions.BinomialHalfEnvelope
import SampLib.Samplers.UniformFin
import SampLib.Samplers.Geometric
import SampLib.Samplers.VonNeumann

/-! # The signed block proposal for half-binomial rejection

A block, a rank within the block, and a sign encode every integer exactly once.
This separates the proposal's elementary geometry from its acceptance envelope.
-/

namespace SampLib.BinomialHalfProposal

noncomputable section

open BinomialHalfEnvelope

/-- Positive offsets begin at the middle; negative offsets begin one place below it. -/
def signedOffset (middle : ℕ) : ℕ × Bool ≃ ℤ where
  toFun t := if t.2 then (middle : ℤ) + t.1 else (middle : ℤ) - t.1 - 1
  invFun z := if (middle : ℤ) ≤ z then ((z - middle).toNat, true)
    else (((middle : ℤ) - z - 1).toNat, false)
  left_inv := by
    rintro ⟨d, sign⟩
    cases sign <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [ite_eq_right (by omega)]
      congr 1
      omega
    · rw [ite_eq_left (by omega)]
      congr 1
      omega
  right_inv z := by
    by_cases hz : (middle : ℤ) ≤ z
    · simp only [hz, ↓reduceIte]
      omega
    · simp only [hz, ↓reduceIte, Bool.false_eq_true]
      omega

/-- The source's block/rank/sign representation of an integer candidate. -/
def candidate (n : ℕ) (t : ℕ × (Fin (width n) × Bool)) : ℤ :=
  if t.2.2 then (n / 2 : ℕ) + (t.1 * width n + t.2.1 : ℕ)
    else (n / 2 : ℕ) - (t.1 * width n + t.2.1 : ℕ) - (1 : ℤ)

/-- Decoding introduces no collisions, including at the middle of the support. -/
def candidateEquiv (n : ℕ) : (ℕ × (Fin (width n) × Bool)) ≃ ℤ :=
  letI : NeZero (width n) := ⟨Nat.ne_of_gt (width_pos n)⟩
  (Equiv.prodAssoc ℕ (Fin (width n)) Bool).symm.trans
    ((Equiv.prodCongr (Nat.divModEquiv (width n)).symm (Equiv.refl Bool)).trans
      (signedOffset (n / 2)))

theorem candidateEquiv_apply (n : ℕ) (t : ℕ × (Fin (width n) × Bool)) :
    candidateEquiv n t = candidate n t := by
  rfl

/-- Every candidate has precisely one source proposal. -/
theorem candidate_injective (n : ℕ) : Function.Injective (candidate n) :=
  (candidateEquiv n).injective

section distribution

open MeasureTheory
open scoped ENNReal

/-- Independent block, rank, and sign, in the source's sampling order. -/
def law (n : ℕ) : Measure (ℕ × (Fin (width n) × Bool)) :=
  (Geometric.law VonNeumann.fairBias).prod
    ((UniformFin.law (width n)).prod VonNeumann.law)

instance (n : ℕ) : IsProbabilityMeasure (law n) := by
  have : NeZero (width n) := ⟨Nat.ne_of_gt (width_pos n)⟩
  unfold law
  infer_instance

/-- Each valid rank and sign has the same conditional probability. -/
theorem law_singleton (n : ℕ) (t : ℕ × (Fin (width n) × Bool)) :
    law n {t} = ENNReal.ofReal ((1 / 2 : ℝ) ^ (t.1 + 2) / width n) := by
  obtain ⟨block, rank, sign⟩ := t
  have hp : VonNeumann.fairBias ≠ 0 := by
    intro h
    have : (1 / 2 : ℝ) = 0 := congrArg Subtype.val h
    norm_num at this
  simp only [law, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Geometric.law, ProbabilityTheory.geometricMeasure_singleton hp,
    UniformFin.law_singleton]
  have hs : VonNeumann.law {sign} = ENNReal.ofReal (1 / 2 : ℝ) := by
    cases sign <;> norm_num [VonNeumann.law, RealCoin.law, RealCoin.pmf,
      VonNeumann.fairBias]
  rw [hs]
  simp only [VonNeumann.fairBias, sub_half]
  have hw : (0 : ℝ) < width n := by exact_mod_cast width_pos n
  rw [← ENNReal.ofReal_natCast (width n), ← ENNReal.ofReal_inv_of_pos hw,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [pow_add]
  norm_num
  ring

end distribution

end

end SampLib.BinomialHalfProposal
