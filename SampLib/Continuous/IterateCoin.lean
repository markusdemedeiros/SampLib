import SampLib.Uniform.RealCoin
import Samplers.Continuous
import Metrology.Iris.LocalBI

/-! # Finite Bernoulli iteration

All `n` input flips must succeed. The expectation recurrence factors the success
probability as `p * p^n`; finite induction supplies total correctness.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow)
open scoped ENNReal

namespace SampLib.IterateCoin

noncomputable section

/-- Probability that all `n` flips succeed. -/
def bias (p : unitInterval) (n : ℕ) : unitInterval :=
  ⟨(p : ℝ) ^ n, pow_nonneg p.2.1 _, pow_le_one₀ p.2.1 p.2.2⟩

abbrev law (p : unitInterval) (n : ℕ) := RealCoin.law (bias p n)

def credit (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  RealCoin.credit (bias p n) F

def continuation (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then credit p n F else F false

@[simp] theorem credit_zero (p : unitInterval) (F : Bool → ℝ≥0∞) :
    credit p 0 F = F true := by
  simp [credit, RealCoin.credit, RealCoin.pmf, bias]

/-- One flip followed by `n` successes preserves the Bernoulli(`p^(n+1)`) expectation. -/
theorem expectation (p : unitInterval) (n : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, continuation p n F b ∂RealCoin.law p = credit p (n + 1) F := by
  have hpow : ofReal ((p : ℝ) ^ (n + 1)) =
      ofReal (p : ℝ) * ofReal ((p : ℝ) ^ n) := by
    rw [ofReal_pow p.2.1, ofReal_pow p.2.1, pow_succ]
    ring
  have hfalse : ofReal (p : ℝ) * ofReal (1 - (p : ℝ) ^ n) +
      ofReal (1 - (p : ℝ)) = ofReal (1 - (p : ℝ) ^ (n + 1)) := by
    rw [← ofReal_mul p.2.1,
      ← ofReal_add (mul_nonneg p.2.1 (sub_nonneg.mpr (pow_le_one₀ p.2.1 p.2.2)))
        (sub_nonneg.mpr p.2.2)]
    congr 1
    ring
  rw [RealCoin.lintegral_law]
  simp only [RealCoin.credit, RealCoin.pmf, continuation, credit, bias,
    Bool.false_eq_true, ite_true, ite_false]
  rw [hpow, ← hfalse]
  ring

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_iterateCoin (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p n F) -∗ tglWp E pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [← expectation p n F] at Hcredit
    iapply (hcoin.wp (continuation p n F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      isimp only [continuation, ite_true] at Hcredit
      iapply IH $$ Hcredit

/-- Typed specification for the all-successes factory, including both coin endpoints. -/
theorem iterateCoin_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.iterateCoin &coin.fst #int (n : ℤ))
      (law p n) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law, credit] using
      wand_entails (twp_iterateCoin E p coin hcoin n F)

end specification

end

end SampLib.IterateCoin
