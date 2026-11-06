import SampLib.Uniform.RealCoin
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Binomial trial sums

The law is the `n`-fold convolution of a Bernoulli count: a successful trial
shifts the previous sum by one, and a failed trial leaves it unchanged.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Binomial

noncomputable section

section mathematics

open MeasureTheory Measure

/-- The sum of `n` independent Bernoulli(`p`) indicators. -/
def law (p : unitInterval) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => (RealCoin.pmf p true • (law p n).map Nat.succ) +
      (RealCoin.pmf p false • law p n)

instance (p : unitInterval) (n : ℕ) : IsProbabilityMeasure (law p n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    simpa [law, Measure.map_apply (measurable_of_countable Nat.succ)] using RealCoin.pmf_sum p

/-- Conditional expectation after the first indicator. -/
def continuation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  ∫⁻ k, F (if b then k + 1 else k) ∂law p n

@[simp] theorem expectation_zero (p : unitInterval) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law p 0 = F 0 := by simp [law]

/-- Splitting off one indicator preserves the binomial expectation. -/
theorem expectation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ b, continuation p n F b ∂RealCoin.law p = ∫⁻ k, F k ∂law p (n + 1) := by
  rw [RealCoin.lintegral_law]
  simp [law, RealCoin.credit, continuation,
    lintegral_map (measurable_of_countable F) (measurable_of_countable Nat.succ),
    smul_eq_mul, Nat.succ_eq_add_one]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_binomial (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law p n) -∗ tglWp E pl(&Occil.binomial &coin.fst #int (n : ℤ))
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [expectation_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [← expectation p n F] at Hcredit
    iapply (hcoin.wp (continuation p n F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.binomial &coin.fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [continuation] at Hcredit
      iapply IH $$ Hcredit
    iintro %v ⟨%k, %hv, Hcredit⟩
    subst v
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists k
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pures
      rw [← Nat.cast_add_one]
      twp_value
      imodintro
      iexists (k + 1)
      isimp only [ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed binomial specification for every trial count and both coin endpoints. -/
theorem binomial_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.binomial &coin.fst #int (n : ℤ))
      (law p n) (fun k => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_binomial E p coin hcoin n F)

end specification

end

end SampLib.Binomial
