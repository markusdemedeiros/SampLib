import SampLib.Bernoulli.EnvelopeFactory
import Mathlib.Analysis.SpecificLimits.Basic

open Finset Filter ProbLang
open scoped Topology ENNReal

namespace ExactEnvelopeAsymptoticCallers

open SampLib SampLib.EnvelopeFactory FactoryFractions

noncomputable section

private def error (t : ℕ) : ℚ := (1 / 2) ^ t
private def lower (t : ℕ) : ℚ := (1 - error t) / 3
private def upper (t : ℕ) : ℚ := (1 + 2 * error t) / 3

private theorem error_bounds (t : ℕ) : 0 < error t ∧ error t ≤ 1 := by
  constructor
  · exact pow_pos (by norm_num) _
  · exact pow_le_one₀ (by norm_num) (by norm_num)

private theorem error_step (t : ℕ) : error (t + 1) = error t / 2 := by
  simp [error, pow_succ, div_eq_mul_inv]

private theorem reverse_sum (t : ℕ) (k : Fin (t + 2)) :
    (∑ j : Fin (t + 1), ReverseBinomial.coefficient t (t + 1) k j) = 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact ReverseBinomial.coefficient_sum_degree _ _ _ (by omega) (by omega)

def coefficients : Coefficients where
  degree := id
  initial_degree := rfl
  grows t := by change t < t + 1; omega
  lower t _ := lower t
  upper t _ := upper t
  bounds t _ := by
    have he := error_bounds t
    dsimp [lower, upper]
    constructor
    · linarith
    constructor <;> linarith
  lower_initial _ := by norm_num [lower, error]
  upper_initial _ := by norm_num [upper, error]
  lower_consistent t k := by
    change (∑ j : Fin (t + 1), ReverseBinomial.coefficient t (t + 1) k j * lower t) ≤ _
    rw [← sum_mul, reverse_sum, one_mul]
    have he := (error_bounds t).1
    dsimp [lower]
    rw [error_step]
    linarith
  upper_consistent t k := by
    change _ ≤ ∑ j : Fin (t + 1), ReverseBinomial.coefficient t (t + 1) k j * upper t
    rw [← sum_mul, reverse_sum, one_mul]
    have he := (error_bounds t).1
    dsimp [upper]
    rw [error_step]
    linarith

private theorem means (t : ℕ) (p : unitInterval) :
    coefficients.lowerMean t p = (lower t : ℝ) ∧
      coefficients.upperMean t p = (upper t : ℝ) := by
  constructor
  · change (∑ k : Fin (t + 1), bernstein t k p * (lower t : ℝ)) = _
    rw [← sum_mul, bernstein.probability, one_mul]
  · change (∑ k : Fin (t + 1), bernstein t k p * (upper t : ℝ)) = _
    rw [← sum_mul, bernstein.probability, one_mul]

private theorem error_tendsto : Tendsto (fun t => (error t : ℝ)) atTop (𝓝 0) := by
  simpa [error] using tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)

def parameters : Parameters where
  toCoefficients := coefficients
  target _ := ⟨1 / 3, by norm_num, by norm_num⟩
  lower_converges p := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub error_tendsto).div_const 3
    simp only [sub_zero] at h
    apply h.congr
    intro t
    rw [(means t p).1]
    norm_cast
  upper_converges p := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_const_nhds.mul error_tendsto :
        Tendsto (fun t => (2 : ℝ) * (error t : ℝ)) atTop (𝓝 (2 * 0)))).div_const 3
    simp only [mul_zero, add_zero] at h
    apply h.congr
    intro t
    rw [(means t p).2]
    norm_cast

example (t : ℕ) (k : Fin (parameters.degree t + 1)) :
    0 < parameters.upper t k - parameters.lower t k := by
  change 0 < upper t - lower t
  dsimp [upper, lower]
  linarith [(error_bounds t).1]

def realization : parameters.toCoefficients.Realization where
  raw t _ high := Fraction.ofRat (if high then upper t else lower t)
  value _ _ _ _ := by simp [parameters, coefficients]

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Every finite row has positive width; only the convergence contract resolves the loop. -/
theorem asymptotic_frame (E : CoPset) (p : unitInterval) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E parameters.toCoefficients realization bounds)
    (F : Bool → ℝ≥0∞) (I : IProp GF) :
    iprop(↯ (RealCoin.credit (parameters.target p) F) ∗ I) ⊢
      tglWp E pl(&Occil.FactoryExtra.envelopeFactory &coin.fst &bounds.fst #())
        (fun v => iprop((∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)) ∗ I)) := by
  have hs := envelopeFactory_distSpec E parameters realization (fun _ => rfl)
    p coin bounds hcoin hbounds
  iintro ⟨Hcredit, HI⟩
  isimp only [← RealCoin.lintegral_law] at Hcredit
  iapply (hs.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  isplitl [Hcredit]
  · iexists b
    iframe Hcredit
    itrivial
  iframe HI

end callers

#print axioms parameters
#print axioms asymptotic_frame

end
end ExactEnvelopeAsymptoticCallers
