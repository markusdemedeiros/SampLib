import SampLib.Core.Retry
import SampLib.Uniform.FairCoin
import Samplers.Bernoulli.Elementary
import Metrology.Iris.LocalBI

/-!
# The Bernoulli factory `(1-p)/(1+p)`

Retry credit doubles. Input-true exits discard auxiliary credit, keeping the
expectation identity exact even at the endpoint p=1.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.OneMinusOverOnePlus

noncomputable section

/-- Output bias. -/
def bias (p : unitInterval) : unitInterval :=
  ⟨(1 - (p : ℝ)) / (1 + (p : ℝ)), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr p.2.2) (by linarith [p.2.1])
    · exact (div_le_one (by linarith [p.2.1])).2 (by linarith [p.2.1])⟩

/-- Expected continuation credit. -/
def credit (p : unitInterval) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ b, F b ∂RealCoin.law (bias p)

/-- Constant amplification avoids a singular factor at p=1. -/
def terminationFactor : ℝ≥0 := 2

/-- Auxiliary credit is amplified on retry and discarded on input-true exits. -/
def pairCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (bit select : Bool) : ℝ≥0∞ :=
  if select then F (!bit) + (if bit then ε else 0) else
    if bit then F false + ε else credit p F + terminationFactor * ε

/-- Conditional expectation after the input flip. -/
def inputCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (bit : Bool) : ℝ≥0∞ :=
  ∫⁻ select, pairCredit p F ε bit select ∂RealCoin.law VonNeumann.fairBias

/-- One round preserves the target expectation and auxiliary termination credit. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ bit, inputCredit p F ε bit ∂RealCoin.law p = credit p F + ε := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  have hh0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have ht : ofReal (bias p : ℝ) =
      ofReal (1 - (p : ℝ)) * ofReal (1 / 2 : ℝ) * (1 + ofReal (bias p : ℝ)) := by
    rw [mul_add, mul_one, ← ofReal_mul hq0,
      ← ofReal_mul (mul_nonneg hq0 hh0),
      ← ofReal_add (mul_nonneg hq0 hh0)
        (mul_nonneg (mul_nonneg hq0 hh0) (bias p).2.1)]
    congr 1
    dsimp [bias]
    field_simp
    ring
  have hf : ofReal (1 - (bias p : ℝ)) = ofReal (p : ℝ) +
      ofReal (1 - (p : ℝ)) * ofReal (1 / 2 : ℝ) * ofReal (1 - (bias p : ℝ)) := by
    rw [← ofReal_mul hq0, ← ofReal_mul (mul_nonneg hq0 hh0),
      ← ofReal_add hp0 (mul_nonneg (mul_nonneg hq0 hh0) (sub_nonneg.mpr (bias p).2.2))]
    congr 1
    dsimp [bias]
    field_simp
    ring
  have hh : ofReal (1 / 2 : ℝ) + ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ofReal_add hh0 hh0]
    norm_num
  have hsum := RealCoin.pmf_sum p
  norm_num [RealCoin.pmf] at hsum
  have hx : ofReal (1 / 2 : ℝ) * 2 = 1 := by simpa only [mul_two] using hh
  rw [RealCoin.lintegral_law]
  norm_num [inputCredit, pairCredit, credit, RealCoin.lintegral_law,
    RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias, terminationFactor]
  rw [← Bool.univ_eq, MeasureTheory.measure_univ, mul_one]
  calc
    _ = (ofReal (1 - (p : ℝ)) * ofReal (1 / 2 : ℝ) *
          (1 + ofReal (bias p : ℝ))) * F true +
        (ofReal (p : ℝ) + ofReal (1 - (p : ℝ)) * ofReal (1 / 2 : ℝ) *
          ofReal (1 - (bias p : ℝ))) * F false +
        (ofReal (p : ℝ) + ofReal (1 - (p : ℝ))) * ε := by
      simp only [mul_add, ← mul_assoc, hx, one_mul]
      ring
    _ = _ := by rw [← ht, ← hf, hsum, one_mul]

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by
  cases b <;> rfl

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification, including p=0 and p=1. -/
theorem twp_oneMinusOverOnePlus (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗
      tglWp E pl(&Occil.FactoryExtra.oneMinusOverOnePlus &coin.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iapply Retry.twp_loop (k := terminationFactor) solve_not_value
    (one_lt_two : (1 : ℝ≥0) < terminationFactor)
  iintro !> %ε %hε IH Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [← expectation p F ε] at Hcredit
  iapply (hcoin.wp (inputCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %bit Hcredit
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  isimp only [inputCredit] at Hcredit
  iapply ((FairCoin.fairCoin_distSpec E).wp (pairCredit p F ε bit)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %select Hcredit
  cases select
  · twp_pure
    cases bit
    · twp_pure
      isimp only [pairCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_bind pl(&Occil.FactoryExtra.oneMinusOverOnePlus &coin.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hcredit
    · twp_pures
      isimp only [pairCredit, Bool.false_eq_true, ite_false, ite_true] at Hcredit
      ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      ipureintro
      rfl
  · twp_pures
    isimp only [pairCredit, ite_true] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_value
    imodintro
    iexists !bit
    iframe Hcredit
    ipureintro
    simp only [Val.ext_iff, bool_not]

/-- Typed distribution specification from an abstract p-coin. -/
theorem oneMinusOverOnePlus_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.oneMinusOverOnePlus &coin.fst #())
      (RealCoin.law (bias p)) Val.bool where
  spec F _ := wand_entails (twp_oneMinusOverOnePlus E p coin hcoin F)

end specification

end

end SampLib.OneMinusOverOnePlus
