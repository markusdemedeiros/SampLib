import SampLib.Samplers.RealCoin
import Samplers.Discrete.Bounded
import Metrology.Iris.LocalBI

/-! # Capped geometric failures

The law counts failures before success, capped at `n`. Its recurrence separates
immediate success from a failed trial followed by a shifted capped count.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.BoundedGeometric

noncomputable section

section mathematics

open MeasureTheory Measure

/-- The geometric failure count capped at `n`, including the mass at the cap. -/
def law (p : unitInterval) : ℕ → Measure ℕ
  | 0 => dirac 0
  | n + 1 => (RealCoin.pmf p true • dirac 0) +
      (RealCoin.pmf p false • (law p n).map Nat.succ)

instance (p : unitInterval) (n : ℕ) : IsProbabilityMeasure (law p n) := by
  induction n with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH
    constructor
    simpa [law, Measure.map_apply (measurable_of_countable Nat.succ)] using RealCoin.pmf_sum p

/-- Conditional continuation credit after the first flip. -/
def continuation (p : unitInterval) (n : ℕ) (F : ℕ → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F 0 else ∫⁻ k, F (k + 1) ∂law p n

@[simp] theorem expectation_zero (p : unitInterval) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law p 0 = F 0 := by simp [law]

/-- One success/failure split preserves the capped geometric expectation. -/
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

private theorem one_add_natCast (n : ℕ) : (1 : ℤ) + n = ((n + 1 : ℕ) : ℤ) := by omega

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_boundedGeometric (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law p n) -∗
      tglWp E pl(&Occil.boundedGeometric &coin.fst #int (n : ℤ))
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
    cases b
    · twp_pure
      twp_pure
      rw [Nat.cast_add_one, add_sub_cancel_right]
      twp_bind pl(&Occil.boundedGeometric &coin.fst #int (n : ℤ))
      iapply tglWp_wand
      isplitl [Hcredit]
      · isimp only [continuation, Bool.false_eq_true, ite_false] at Hcredit
        iapply IH $$ Hcredit
      iintro %v ⟨%k, %hv, Hcredit⟩
      subst v
      twp_pures
      rw [one_add_natCast]
      twp_value
      imodintro
      iexists (k + 1)
      iframe Hcredit
      itrivial
    · twp_pures
      twp_value
      imodintro
      iexists 0
      isimp only [continuation, ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed specification for every cap and every input bias, including `p = 0`. -/
theorem boundedGeometric_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.boundedGeometric &coin.fst #int (n : ℤ))
      (law p n) (fun k => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_boundedGeometric E p coin hcoin n F)

end specification

end

end SampLib.BoundedGeometric
