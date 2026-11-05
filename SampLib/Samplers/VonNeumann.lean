import SampLib.Samplers.RealCoin
import Samplers.Bernoulli.Basic
import Metrology.Iris.LocalBI

/-!
# Von Neumann's fair-coin extractor

Equal input flips retry; unequal flips return the first result. The expectation
lemma accounts for fairness and amplified retry credit. The CTE proof composes
an abstract coin specification and closes recursion by error amplification.
-/

open Set ProbLang
open ENNReal (ofReal ofReal_add ofReal_mul ofReal_pow coe_nnreal_eq)
open scoped ENNReal NNReal

namespace SampLib.VonNeumann

open RealCoin (pmf lintegral_law)

noncomputable section

section distribution

/-- Fair-coin bias. -/
def fairBias : unitInterval := ⟨1 / 2, by norm_num⟩

/-- Fair-coin law. -/
abbrev law := RealCoin.law fairBias

/-- Expected continuation credit. -/
def credit (F : Bool → ℝ≥0∞) : ℝ≥0∞ := RealCoin.credit fairBias F

end distribution

section termination

/-- Probability of equal input flips. -/
def retryProbability (p : unitInterval) : ℝ := (p : ℝ) ^ 2 + (1 - (p : ℝ)) ^ 2

private theorem retryProbability_pos (p : unitInterval) : 0 < retryProbability p := by
  dsimp [retryProbability]
  nlinarith [sq_nonneg ((p : ℝ) - 1 / 2)]

/-- Amplification factor for retry credit. -/
def terminationFactor (p : unitInterval) : ℝ≥0 :=
  ⟨1 / retryProbability p, div_nonneg zero_le_one (retryProbability_pos p).le⟩

private theorem one_lt_terminationFactor (p : unitInterval) (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) : 1 < terminationFactor p := by
  have hq : retryProbability p < 1 := by
    dsimp [retryProbability]
    nlinarith [mul_pos hp0 (sub_pos.mpr hp1)]
  exact_mod_cast (one_lt_div (retryProbability_pos p)).mpr hq

end termination

section conservation

/-- Credit after both flips, amplified on retries. -/
def pairCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (a b : Bool) : ℝ≥0∞ :=
  if a = b then credit F + terminationFactor p * ε else F a

/-- Conditional expectation after the first flip. -/
def firstCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) (a : Bool) : ℝ≥0∞ :=
  ∫⁻ b, pairCredit p F ε a b ∂RealCoin.law p

/-- The two flips conserve the fair expectation and auxiliary termination credit. -/
theorem lintegral_firstCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ a, firstCredit p F ε a ∂RealCoin.law p = credit F + ε := by
  have hq : ofReal (retryProbability p) = pmf p true ^ 2 + pmf p false ^ 2 := by
    simp [retryProbability, pmf, ofReal_add (sq_nonneg _) (sq_nonneg _),
      ofReal_pow p.2.1, ofReal_pow (sub_nonneg.mpr p.2.2)]
  have hh : ofReal (1 / 2 : ℝ) + ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hfair : ofReal (retryProbability p) * ofReal (1 / 2 : ℝ) +
      pmf p true * pmf p false = ofReal (1 / 2 : ℝ) := by
    calc
      _ = (pmf p true ^ 2 + pmf p false ^ 2) * ofReal (1 / 2 : ℝ) +
          (pmf p true * pmf p false) * (ofReal (1 / 2 : ℝ) + ofReal (1 / 2 : ℝ)) := by
        rw [hq, hh, mul_one]
      _ = (pmf p true + pmf p false) ^ 2 * ofReal (1 / 2 : ℝ) := by ring
      _ = _ := by rw [RealCoin.pmf_sum]; simp
  have hamp : ofReal (retryProbability p) * (terminationFactor p : ℝ≥0∞) = 1 := by
    rw [coe_nnreal_eq]
    change ofReal (retryProbability p) * ofReal (1 / retryProbability p) = 1
    rw [← ofReal_mul (retryProbability_pos p).le]
    simp [(retryProbability_pos p).ne']
  have hcredit : credit F = ofReal (1 / 2 : ℝ) * (F true + F false) := by
    norm_num [credit, RealCoin.credit, pmf, fairBias, mul_add]
  calc
    _ = (ofReal (retryProbability p) * ofReal (1 / 2 : ℝ) +
          pmf p true * pmf p false) * (F true + F false) +
        (ofReal (retryProbability p) * (terminationFactor p : ℝ≥0∞)) * ε := by
      rw [hq]
      norm_num [firstCredit, lintegral_law, RealCoin.credit, pairCredit, credit, pmf, fairBias]
      ring
    _ = _ := by rw [hfair, hamp, one_mul, hcredit]

end conservation

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

private theorem bool_beq {rT : Type _} [BEq rT] (a b : Bool) :
    ((BaseLit.bool a : BaseLit rT) == .bool b) = (a == b) := rfl

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification from an abstract input-coin spec, for `0 < p < 1`. -/
theorem twp_vonNeumann (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit F) -∗ tglWp E pl(&Occil.vonNeumann &coin.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_terminationFactor p hp0 hp1) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  icombine Hcredit Hterm as Hcredit
  isimp only [← lintegral_firstCredit p F ε] at Hcredit
  iapply (hcoin.wp (firstCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %a Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [firstCredit] at Hcredit
  iapply (hcoin.wp (pairCredit p F ε a) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pures
  rw [bool_beq]
  by_cases hab : a = b
  · rw [beq_iff_eq.mpr hab]
    twp_pure
    isimp only [pairCredit, ite_eq_left hab] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_bind pl(&Occil.vonNeumann &coin.fst #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · rw [beq_eq_false_iff_ne.mpr hab]
    twp_pures
    twp_value
    imodintro
    iexists a
    isimp only [pairCredit, ite_eq_right hab] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed distribution specification for the fair output. -/
theorem vonNeumann_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.vonNeumann &coin.fst #()) law Val.bool where
  spec F _ := by
    simpa only [lintegral_law, credit] using
      wand_entails (twp_vonNeumann E p coin hp0 hp1 hcoin F)

end specification

end

end SampLib.VonNeumann
