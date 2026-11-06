import SampLib.Bernoulli.EvenParity
import SampLib.Uniform.FairCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Reciprocal Bernoulli factory

A fair flip either returns `true`, or tests the input coin and retries on failure.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul)
open scoped ENNReal NNReal

namespace SampLib.OneDivOnePlus

open RealCoin (pmf lintegral_law)

noncomputable section

abbrev bias := EvenParity.bias
abbrev law (p : unitInterval) := RealCoin.law (bias p)
abbrev credit (p : unitInterval) := RealCoin.credit (bias p)

private def retryProbability (p : unitInterval) : ℝ := (1 - (p : ℝ)) / 2

/-- Credit assigned to the input coin after a failed fair flip. -/
def coinCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else credit p F + 2 * ε

/-- Credit assigned to the fair flip. -/
def fairCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F true else ∫⁻ a, coinCredit p F ε a ∂RealCoin.law p

/-- The fair/input mixture preserves the reciprocal bias and spends at most `ε` on retrying. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ b, fairCredit p F ε b ∂RealCoin.law VonNeumann.fairBias ≤ credit p F + ε := by
  have hp0 := p.2.1
  have hp1 := sub_nonneg.mpr p.2.2
  have hq : 0 ≤ retryProbability p := div_nonneg hp1 (by norm_num)
  have ht : 0 ≤ 1 / (1 + (p : ℝ)) := (bias p).2.1
  have hf : 0 ≤ 1 - 1 / (1 + (p : ℝ)) := sub_nonneg.mpr (bias p).2.2
  have hsplit : ofReal (retryProbability p) =
      ofReal (1 / 2 : ℝ) * pmf p false := by
    rw [show retryProbability p = (1 / 2 : ℝ) * (1 - (p : ℝ)) by
      dsimp [retryProbability]; ring, ofReal_mul (by norm_num)]
    simp [pmf]
  have htrue : ofReal (retryProbability p) * pmf (bias p) true + ofReal (1 / 2 : ℝ) =
      pmf (bias p) true := by
    change ofReal (retryProbability p) * ofReal (1 / (1 + (p : ℝ))) +
      ofReal (1 / 2 : ℝ) = ofReal (1 / (1 + (p : ℝ)))
    rw [← ofReal_mul hq,
      ← ofReal_add (mul_nonneg hq ht) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    dsimp [retryProbability, bias, EvenParity.bias]
    field_simp
    ring
  have hfalse : ofReal (retryProbability p) * pmf (bias p) false +
      ofReal (1 / 2 : ℝ) * pmf p true = pmf (bias p) false := by
    change ofReal (retryProbability p) * ofReal (1 - 1 / (1 + (p : ℝ))) +
      ofReal (1 / 2 : ℝ) * ofReal (p : ℝ) = ofReal (1 - 1 / (1 + (p : ℝ)))
    rw [← ofReal_mul hq, ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (mul_nonneg hq hf) (mul_nonneg (by norm_num) hp0)]
    congr 1
    dsimp [retryProbability, bias, EvenParity.bias]
    field_simp
    ring
  have hterm : ofReal (retryProbability p) * 2 ≤ 1 := by
    calc
      _ = ofReal (retryProbability p * 2) := by rw [ofReal_mul hq]; norm_num
      _ ≤ _ := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        dsimp [retryProbability]
        nlinarith
  calc
    _ = (ofReal (retryProbability p) * pmf (bias p) true + ofReal (1 / 2 : ℝ)) * F true +
        (ofReal (retryProbability p) * pmf (bias p) false +
          ofReal (1 / 2 : ℝ) * pmf p true) * F false +
        (ofReal (retryProbability p) * 2) * ε := by
      rw [hsplit]
      norm_num [fairCredit, coinCredit, lintegral_law, RealCoin.credit, pmf, VonNeumann.fairBias]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      exact add_le_add le_rfl (mul_le_of_le_one_left' hterm)

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The reciprocal factory is total for every input bias, including both endpoints. -/
theorem twp_oneDivOnePlus (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.oneDivOnePlus &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  twp_pure
  twp_pure
  twp_pure
  simp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation p F ε) $$ Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp (fairCredit p F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %b Hcredit
  cases b
  · twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [fairCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hcoin.wp (coinCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
    iintro %a Hcredit
    cases a
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.oneDivOnePlus &coin.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [coinCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [fairCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed distribution specification. -/
theorem oneDivOnePlus_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.oneDivOnePlus &coin.fst #()) (law p) Val.bool where
  spec F _ := by
    simpa only [lintegral_law] using wand_entails (twp_oneDivOnePlus E p coin hcoin F)

end specification

end

end SampLib.OneDivOnePlus
