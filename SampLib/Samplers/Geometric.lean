import SampLib.Samplers.RealCoin
import SampLib.Distributions.Geometric
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-!
# Geometric failures before the first success

The input coin is abstract. Success receives spare termination credit; failure
amplifies it by `1+p`. This treats `p=1` without a separate termination proof.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow)
open scoped ENNReal NNReal

namespace SampLib.Geometric

open RealCoin (pmf lintegral_law)

noncomputable section

abbrev law := ProbabilityTheory.geometricMeasure

/-- Expected continuation credit under the geometric law. -/
def credit (p : unitInterval) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ n, F n ∂law p

/-- Amplification remains finite and strictly exceeds one, including at `p=1`. -/
def terminationFactor (p : unitInterval) : ℝ≥0 := 1 + unitInterval.toNNReal p

private theorem one_lt_terminationFactor (p : unitInterval) (hp : 0 < (p : ℝ)) :
    1 < terminationFactor p := by
  change 1 < 1 + unitInterval.toNNReal p
  exact lt_add_of_pos_right _ (by exact_mod_cast hp)

/-- Credit after the coin: stop at zero, or continue with the shifted result. -/
def coinCredit (p : unitInterval) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : Bool → ℝ≥0∞
  | true => F 0 + pmf p true * ε
  | false => credit p (fun n => F (n + 1)) + terminationFactor p * ε

section conservation

open MeasureTheory ProbabilityTheory

/-- The geometric recurrence and `p²+(1-p)(1+p)=1` preserve all continuation credits. -/
theorem lintegral_coinCredit (p : unitInterval) (hp : 0 < (p : ℝ))
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, coinCredit p F ε b ∂RealCoin.law p = credit p F + ε := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  have hrec : credit p F = pmf p true * F 0 +
      pmf p false * credit p (fun n => F (n + 1)) := by
    simpa only [credit, law, pmf, ite_true, Bool.false_eq_true, ite_false] using
      lintegral_geometricMeasure_succ p hpne F
  have hk : (terminationFactor p : ℝ≥0∞) = 1 + pmf p true := by
    simp [terminationFactor, ENNReal.coe_nnreal_eq, pmf, ofReal_add zero_le_one p.2.1]
  have hterm : pmf p true * pmf p true + pmf p false * terminationFactor p = 1 := by
    calc
      _ = pmf p true * (pmf p true + pmf p false) + pmf p false := by rw [hk]; ring
      _ = _ := by simp only [RealCoin.pmf_sum, mul_one]
  rw [lintegral_law]
  calc
    _ = (pmf p true * F 0 + pmf p false * credit p (fun n => F (n + 1))) +
        (pmf p true * pmf p true + pmf p false * terminationFactor p) * ε := by
      simp [RealCoin.credit, coinCredit]
      ring
    _ = _ := by rw [← hrec, hterm, one_mul]

end conservation

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Geometric failure count from an abstract positive-probability coin. -/
theorem twp_geometric (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.geometric &coin.fst #())
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert! %F
  iapply ErrorCredit.Induction.simple hε (one_lt_terminationFactor p hp) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %F Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Hcredit
  isimp only [← lintegral_coinCredit p hp F ε] at Hcredit
  iapply (hcoin.wp (coinCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [coinCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&Occil.geometric &coin.fst #())
    iapply tglWp_wand
    isplitl [IH Hcredit Hterm]
    · iapply IH $$ Hterm %(fun n => F (n + 1)) Hcredit
    iintro %v ⟨%n, %hv, Hcredit⟩
    subst v
    twp_pures
    rw [add_comm (1 : ℤ), ← Nat.cast_add_one]
    twp_value
    imodintro
    iexists n + 1
    iframe Hcredit
    itrivial
  · isimp only [coinCredit] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    iframe Hcredit
    itrivial

/-- Typed geometric distribution specification, including `p=1`. -/
theorem geometric_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.geometric &coin.fst #()) (law p)
      (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    simpa only [credit] using wand_entails (twp_geometric E p hp coin hcoin F)

end specification

end

end SampLib.Geometric
