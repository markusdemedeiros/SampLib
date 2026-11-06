import SampLib.Samplers.RealCoin
import SampLib.Distributions.Geometric
import Samplers.Continuous
import Metrology.Iris.LocalBI

/-! # Successes before the first failure

The count starts at any integer offset. A false input coin stops; true retries
with an incremented offset. The target geometric law has success bias `1-p`.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.GeometricFailures

open RealCoin (pmf lintegral_law)

noncomputable section

abbrev stopBias (p : unitInterval) := unitInterval.symm p
abbrev law (p : unitInterval) := ProbabilityTheory.geometricMeasure (stopBias p)

def credit (p : unitInterval) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ n, F n ∂law p

section termination

def factor (p : unitInterval) : ℝ≥0 := 1 + unitInterval.toNNReal (stopBias p)

private theorem one_lt_factor (p : unitInterval) (hp : (p : ℝ) < 1) : 1 < factor p := by
  change 1 < 1 + unitInterval.toNNReal (stopBias p)
  apply lt_add_of_pos_right
  have hstop : 0 < (stopBias p : ℝ) := by change 0 < 1 - (p : ℝ); linarith
  exact_mod_cast hstop

end termination

def coinCredit (p : unitInterval) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) : Bool → ℝ≥0∞
  | true => credit p (fun n => F (n + 1)) + factor p * ε
  | false => F 0 + pmf p false * ε

/-- The geometric recurrence and `p(2-p)+(1-p)²=1` conserve all continuation credit. -/
theorem expectation (p : unitInterval) (hp : (p : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, coinCredit p F ε b ∂RealCoin.law p = credit p F + ε := by
  have hstop : (stopBias p : ℝ) > 0 := by change 1 - (p : ℝ) > 0; linarith
  have hne : stopBias p ≠ 0 := by intro h; simp [h] at hstop
  have hrec : credit p F = pmf p false * F 0 +
      pmf p true * credit p (fun n => F (n + 1)) := by
    simpa [credit, law, stopBias, pmf, unitInterval.coe_symm_eq] using
      ProbabilityTheory.lintegral_geometricMeasure_succ (stopBias p) hne F
  have hk : (factor p : ℝ≥0∞) = 1 + pmf p false := by
    simp [factor, coe_nnreal_eq, pmf, stopBias, unitInterval.coe_symm_eq]
    rw [ofReal_add zero_le_one (sub_nonneg.mpr p.2.2), ENNReal.ofReal_one]
  have hterm : pmf p true * factor p + pmf p false * pmf p false = 1 := by
    calc
      _ = (pmf p true + pmf p false) * pmf p false + pmf p true := by rw [hk]; ring
      _ = _ := by rw [RealCoin.pmf_sum, one_mul, add_comm, RealCoin.pmf_sum]
  rw [lintegral_law]
  calc
    _ = (pmf p false * F 0 + pmf p true * credit p (fun n => F (n + 1))) +
        (pmf p true * factor p + pmf p false * pmf p false) * ε := by
      simp [RealCoin.credit, coinCredit]
      ring
    _ = _ := by rw [← hrec, hterm, one_mul]

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The true-run count, with arbitrary integer starting offset and `p < 1`. -/
theorem twp_geometricFailures (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (offset : ℤ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.geometricFailures &coin.fst #offset)
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (offset + n)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert! %offset %F
  iapply ErrorCredit.Induction.simple hε (one_lt_factor p hp) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %offset %F Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Hcredit
  isimp only [← expectation p hp F ε] at Hcredit
  iapply (hcoin.wp (coinCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [coinCredit] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    iframe Hcredit
    ipureintro
    simp
  · isimp only [coinCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_pure
    twp_bind pl(&Occil.geometricFailures &coin.fst #(offset + 1))
    iapply tglWp_wand
    isplitl [IH Hcredit Hterm]
    · iapply IH $$ Hterm %(offset + 1) %(fun n => F (n + 1)) Hcredit
    iintro %v ⟨%n, %hv, Hcredit⟩
    subst v
    twp_value
    imodintro
    iexists n + 1
    iframe Hcredit
    ipureintro
    rw [Nat.cast_add_one, add_right_comm offset (1 : ℤ) (n : ℤ), add_assoc]
    exact Val.ext rfl

/-- Typed geometric-count specification, including deterministic `p=0`. -/
theorem geometricFailures_distSpec (E : CoPset) (p : unitInterval) (hp : (p : ℝ) < 1)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (offset : ℤ) :
    IsDistSpec (GF := GF) E pl(&Occil.geometricFailures &coin.fst #offset) (law p)
      (fun n : ℕ => Val.int (offset + n)) where
  spec F _ := by
    simpa only [credit] using wand_entails (twp_geometricFailures E p hp coin hcoin offset F)

end specification

end

end SampLib.GeometricFailures
