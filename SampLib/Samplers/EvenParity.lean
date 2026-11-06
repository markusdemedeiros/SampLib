import SampLib.Samplers.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-! # Even-parity Bernoulli factory

Pairs of successes retry. The output bias is `1 / (1 + p)` for `p < 1`.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.EvenParity

open RealCoin (pmf lintegral_law)

noncomputable section

/-- The target bias, including the deterministic `p = 0` case. -/
def bias (p : unitInterval) : unitInterval :=
  ⟨1 / (1 + (p : ℝ)),
    (one_div_pos.mpr (by linarith [p.2.1] : 0 < 1 + (p : ℝ))).le,
    (div_le_one (by linarith [p.2.1] : 0 < 1 + (p : ℝ))).2 (by linarith [p.2.1])⟩

abbrev law (p : unitInterval) := RealCoin.law (bias p)

def credit (p : unitInterval) (F : Bool → ℝ≥0∞) := RealCoin.credit (bias p) F

section termination

def factor (p : unitInterval) : ℝ≥0 :=
  ⟨2 / (1 + (p : ℝ) ^ 2), by positivity⟩

private theorem one_lt_factor (p : unitInterval) (hp : (p : ℝ) < 1) : 1 < factor p := by
  have hden : 0 < 1 + (p : ℝ) ^ 2 := by positivity
  have hlt : (p : ℝ) ^ 2 < 1 := by nlinarith [p.2.1]
  exact_mod_cast (one_lt_div hden).2 (by linarith : 1 + (p : ℝ) ^ 2 < 2)

end termination

def pairCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (a b : Bool) : ℝ≥0∞ :=
  if a then if b then credit p F + factor p * ε else F false else F true

def firstCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  if a then ∫⁻ b, pairCredit p F ε true b ∂RealCoin.law p else F true

/-- Pairing successes preserves the target expectation; retry amplification costs at most `ε`. -/
theorem expectation (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ a, firstCredit p F ε a ∂RealCoin.law p ≤ credit p F + ε := by
  have hp0 := p.2.1
  have hp1 := sub_nonneg.mpr p.2.2
  have ht := (bias p).2.1
  have hf := sub_nonneg.mpr (bias p).2.2
  have htrue : ofReal ((p : ℝ) ^ 2) * pmf (bias p) true + pmf p false =
      pmf (bias p) true := by
    simp only [pmf, ite_true, Bool.false_eq_true, ite_false]
    rw [← ofReal_mul (sq_nonneg _), ← ofReal_add (mul_nonneg (sq_nonneg _) ht) hp1]
    congr 1
    dsimp [bias]
    field_simp
    ring
  have hfalse : ofReal ((p : ℝ) ^ 2) * pmf (bias p) false +
      pmf p true * pmf p false = pmf (bias p) false := by
    simp only [pmf, ite_true, Bool.false_eq_true, ite_false]
    rw [← ofReal_mul (sq_nonneg _), ← ofReal_mul hp0,
      ← ofReal_add (mul_nonneg (sq_nonneg _) hf) (mul_nonneg hp0 hp1)]
    congr 1
    dsimp [bias]
    field_simp
    ring
  have hterm : ofReal ((p : ℝ) ^ 2) * (factor p : ℝ≥0∞) ≤ 1 := by
    rw [coe_nnreal_eq]
    change ofReal ((p : ℝ) ^ 2) * ofReal (2 / (1 + (p : ℝ) ^ 2)) ≤ 1
    rw [← ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [← mul_div_assoc]
    apply (div_le_one (by positivity : 0 < 1 + (p : ℝ) ^ 2)).2
    nlinarith [p.2.1, p.2.2]
  calc
    _ = (ofReal ((p : ℝ) ^ 2) * pmf (bias p) true + pmf p false) * F true +
        (ofReal ((p : ℝ) ^ 2) * pmf (bias p) false + pmf p true * pmf p false) * F false +
        (ofReal ((p : ℝ) ^ 2) * (factor p : ℝ≥0∞)) * ε := by
      rw [ofReal_pow hp0, pow_two]
      simp [firstCredit, pairCredit, lintegral_law, credit, RealCoin.credit, pmf]
      ring
    _ ≤ _ := by
      rw [htrue, hfalse]
      change _ ≤ (pmf (bias p) true * F true + pmf (bias p) false * F false) + ε
      exact add_le_add le_rfl (mul_le_of_le_one_left' hterm)

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The parity factory is total for `p < 1`, including `p = 0`. -/
theorem twp_evenParity (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.evenParity &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor p hp) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation p F ε) $$ Htotal
  iapply (hcoin.wp (firstCredit p F ε) (measurable_of_countable _) _) $$ Hsample
  iintro %a Hcredit
  cases a
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    twp_bind pl(&coin.fst #())
    isimp only [firstCredit, ite_true] at Hcredit
    iapply (hcoin.wp (pairCredit p F ε true) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [pairCredit, Bool.false_eq_true, ite_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      isimp only [pairCredit, ite_true] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_bind pl(&Occil.evenParity &coin.fst #())
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm Hcredit

/-- Typed distribution specification. -/
theorem evenParity_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.evenParity &coin.fst #()) (law p) Val.bool where
  spec F _ := by
    simpa only [lintegral_law, credit] using
      wand_entails (twp_evenParity E p coin hp hcoin F)

end specification

end

end SampLib.EvenParity
