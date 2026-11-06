import SampLib.Uniform.FairCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Bernoulli race

A fair selector chooses which input coin to try. Success returns that side;
failure retries. The output bias is `p / (p + q)` whenever `p + q > 0`.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.BernoulliRace

open RealCoin (pmf lintegral_law)

noncomputable section

def bias (p q : unitInterval) : unitInterval :=
  ⟨(p : ℝ) / ((p : ℝ) + q), div_nonneg p.2.1 (add_nonneg p.2.1 q.2.1), by
    by_cases hsum : (p : ℝ) + q = 0
    · simp [hsum]
    · apply (div_le_one (lt_of_le_of_ne (add_nonneg p.2.1 q.2.1) (Ne.symm hsum))).2
      linarith [q.2.1]⟩

abbrev law (p q : unitInterval) := RealCoin.law (bias p q)
abbrev credit (p q : unitInterval) := RealCoin.credit (bias p q)

section termination

private def retryProbability (p q : unitInterval) : ℝ := 1 - ((p : ℝ) + q) / 2

private theorem retryProbability_nonneg (p q : unitInterval) : 0 ≤ retryProbability p q := by
  dsimp [retryProbability]
  linarith [p.2.2, q.2.2]

def factor (p q : unitInterval) : ℝ≥0 :=
  ⟨2 / (1 + retryProbability p q), div_nonneg (by norm_num)
    (by linarith [retryProbability_nonneg p q])⟩

private theorem one_lt_factor (p q : unitInterval) (hsum : 0 < (p : ℝ) + q) :
    1 < factor p q := by
  have hr : retryProbability p q < 1 := by dsimp [retryProbability]; linarith
  have hd : 0 < 1 + retryProbability p q := by linarith [retryProbability_nonneg p q]
  exact_mod_cast (one_lt_div hd).2 (by linarith : 1 + retryProbability p q < 2)

end termination

def coinCredit (p q : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞)
    (side success : Bool) : ℝ≥0∞ :=
  if success then F side else credit p q F + factor p q * ε

def fairCredit (p q : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (side : Bool) : ℝ≥0∞ :=
  if side then ∫⁻ b, coinCredit p q F ε true b ∂RealCoin.law p
  else ∫⁻ b, coinCredit p q F ε false b ∂RealCoin.law q

/-- Both success exits balance the target ratio; failed attempts spend at most `ε`. -/
theorem expectation (p q : unitInterval) (hsum : 0 < (p : ℝ) + q)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ side, fairCredit p q F ε side ∂RealCoin.law VonNeumann.fairBias ≤ credit p q F + ε := by
  have hr := retryProbability_nonneg p q
  have ht : 0 ≤ (p : ℝ) / ((p : ℝ) + q) := (bias p q).2.1
  have hf : 0 ≤ 1 - (p : ℝ) / ((p : ℝ) + q) := sub_nonneg.mpr (bias p q).2.2
  have hsplit : ofReal (retryProbability p q) =
      ofReal (1 / 2 : ℝ) * (pmf p false + pmf q false) := by
    rw [show retryProbability p q = (1 / 2 : ℝ) * ((1 - (p : ℝ)) + (1 - (q : ℝ))) by
      dsimp [retryProbability]; ring, ofReal_mul (by norm_num),
      ofReal_add (sub_nonneg.mpr p.2.2) (sub_nonneg.mpr q.2.2)]
    simp [pmf]
  have htrue : ofReal (retryProbability p q) * pmf (bias p q) true +
      ofReal (1 / 2 : ℝ) * pmf p true = pmf (bias p q) true := by
    change ofReal (retryProbability p q) * ofReal ((p : ℝ) / ((p : ℝ) + q)) +
      ofReal (1 / 2 : ℝ) * ofReal (p : ℝ) = ofReal ((p : ℝ) / ((p : ℝ) + q))
    rw [← ofReal_mul hr, ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (mul_nonneg hr ht) (mul_nonneg (by norm_num) p.2.1)]
    congr 1
    dsimp [retryProbability]
    field_simp [hsum.ne']
    ring
  have hfalse : ofReal (retryProbability p q) * pmf (bias p q) false +
      ofReal (1 / 2 : ℝ) * pmf q true = pmf (bias p q) false := by
    change ofReal (retryProbability p q) * ofReal (1 - (p : ℝ) / ((p : ℝ) + q)) +
      ofReal (1 / 2 : ℝ) * ofReal (q : ℝ) = ofReal (1 - (p : ℝ) / ((p : ℝ) + q))
    rw [← ofReal_mul hr, ← ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ofReal_add (mul_nonneg hr hf) (mul_nonneg (by norm_num) q.2.1)]
    congr 1
    dsimp [retryProbability]
    field_simp [hsum.ne']
    ring
  have hterm : ofReal (retryProbability p q) * (factor p q : ℝ≥0∞) ≤ 1 := by
    rw [coe_nnreal_eq]
    change ofReal (retryProbability p q) * ofReal (2 / (1 + retryProbability p q)) ≤ 1
    rw [← ofReal_mul hr, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_one (by linarith : 0 < 1 + retryProbability p q)).2
    dsimp [retryProbability]
    linarith [p.2.1, q.2.1]
  calc
    _ = (ofReal (retryProbability p q) * pmf (bias p q) true +
          ofReal (1 / 2 : ℝ) * pmf p true) * F true +
        (ofReal (retryProbability p q) * pmf (bias p q) false +
          ofReal (1 / 2 : ℝ) * pmf q true) * F false +
        (ofReal (retryProbability p q) * (factor p q : ℝ≥0∞)) * ε := by
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

/-- The race is total when at least one input coin can succeed. -/
theorem twp_bernoulliRace (E : CoPset) (p q : unitInterval) (hsum : 0 < (p : ℝ) + q)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p q F) -∗ tglWp E pl(&Occil.bernoulliRace &left.fst &right.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor p q hsum) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  simp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
  twp_bind pl(&Occil.fairCoin #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation p q hsum F ε) $$ Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp (fairCredit p q F ε)
    (measurable_of_countable _) _) $$ Hsample
  iintro %side Hcredit
  cases side
  · twp_pures
    twp_bind pl(&right.fst #())
    isimp only [fairCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply (hright.wp (coinCredit p q F ε false) (measurable_of_countable _) _) $$ Hcredit
    iintro %success Hcredit
    cases success
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.bernoulliRace &left.fst &right.fst #())
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
    twp_bind pl(&left.fst #())
    isimp only [fairCredit, ite_true] at Hcredit
    iapply (hleft.wp (coinCredit p q F ε true) (measurable_of_countable _) _) $$ Hcredit
    iintro %success Hcredit
    cases success
    · twp_pure
      isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.bernoulliRace &left.fst &right.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [coinCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed ratio specification, including zero probability on either individual side. -/
theorem bernoulliRace_distSpec (E : CoPset) (p q : unitInterval) (hsum : 0 < (p : ℝ) + q)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.bernoulliRace &left.fst &right.fst #())
      (law p q) Val.bool where
  spec F _ := by
    simpa only [lintegral_law] using
      wand_entails (twp_bernoulliRace E p q hsum left right hleft hright F)

end specification

end

end SampLib.BernoulliRace
