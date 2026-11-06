import SampLib.Samplers.BernsteinFactory
import Samplers.Bernoulli.Series

/-! # The exact law of a numerical plug-in factory

The target is the Bernstein average of the clamped evaluations at the sampled
empirical proportion. It is generally different from the evaluator at `p`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ApproximateFactory

noncomputable section

/-- Clamp the integer evaluator output to the probability scale. -/
def clamp (scale : ℕ) (v : ℤ) : ℤ :=
  if v < 0 then 0 else if (scale : ℤ) < v then scale else v

private theorem clamp_nonneg (scale : ℕ) (v : ℤ) : 0 ≤ clamp scale v := by
  unfold clamp
  split_ifs <;> omega

private theorem clamp_le (scale : ℕ) (v : ℤ) : clamp scale v ≤ scale := by
  unfold clamp
  split_ifs <;> omega

/-- The rational coin used after evaluating the empirical probability. -/
def componentBias (trials scale : ℕ) [NeZero scale] (f : ℤ → ℤ) (k : ℕ) : unitInterval :=
  RationalCoin.bias (clamp scale (f ((scale : ℤ) * k / trials))) scale
    (clamp_nonneg ..) (Int.natCast_pos.mpr (NeZero.pos scale)) (clamp_le ..)

section mathematics

open MeasureTheory

/-- Binomial mixture of the clamped numerical evaluations. -/
def law (p : unitInterval) (trials scale : ℕ) [NeZero scale] (f : ℤ → ℤ) : Measure Bool :=
  (Binomial.law p trials).bind (fun k => RealCoin.law (componentBias trials scale f k))

instance (p : unitInterval) (trials scale : ℕ) [NeZero scale] (f : ℤ → ℤ) :
    IsProbabilityMeasure (law p trials scale f) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- The exact bias is the finite Bernstein polynomial of the evaluated grid values. -/
theorem success_probability (p : unitInterval) (trials scale : ℕ) [NeZero scale]
    (f : ℤ → ℤ) :
    law p trials scale f {true} = ∑ k ∈ Finset.range (trials + 1),
      ENNReal.ofReal ((trials.choose k : ℝ) * (p : ℝ) ^ k *
        (1 - (p : ℝ)) ^ (trials - k)) *
      ENNReal.ofReal (componentBias trials scale f k : ℝ) := by
  rw [law, Measure.bind_apply (measurableSet_singleton true)
    (measurable_of_countable _).aemeasurable]
  simpa [RealCoin.law, RealCoin.pmf] using Binomial.lintegral_eq_sum p trials
    (fun k => ENNReal.ofReal (componentBias trials scale f k : ℝ))

/-- Only actual binomial counts need an evaluator specification. -/
def countCredit (trials scale : ℕ) [NeZero scale] (f : ℤ → ℤ)
    (F : Bool → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k ≤ trials then RealCoin.credit (componentBias trials scale f k) F else ∞

/-- Conditioning on the empirical count preserves the clamped Bernstein expectation. -/
theorem expectation (p : unitInterval) (trials scale : ℕ) [NeZero scale]
    (f : ℤ → ℤ) (F : Bool → ℝ≥0∞) :
    ∫⁻ k, countCredit trials scale f F k ∂Binomial.law p trials =
      ∫⁻ b, F b ∂law p trials scale f := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [BernsteinFactory.binomial_support p trials] with k hk
  rw [countCredit, ite_eq_left hk, RealCoin.lintegral_law]

end mathematics

private theorem binomial_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.binomial = Occil.binomial :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem binomial_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.binomial : Exp rT) = Occil.binomial :=
  Exp.closeRec_fresh x _ k (by simp [Occil.binomial, Exp.fv])

private theorem nonpositive_test (n : ℕ) [NeZero n] : decide ((n : ℤ) ≤ 0) = false := by
  exact decide_eq_false (by exact_mod_cast Nat.not_le.mpr (NeZero.pos n))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_clamp (E : CoPset) (scale : ℕ) (v : ℤ) :
    ⊢ tglWp E pl(if #int v < #0 then #0 else if #int (scale : ℤ) < #int v
        then #int (scale : ℤ) else #int v)
      (fun w : Val rT => iprop(⌜w = Val.int (clamp scale v)⌝)) := by
  by_cases hneg : v < 0
  · twp_pures
    rw [decide_eq_true hneg]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [clamp, hneg]
  · twp_pures
    rw [decide_eq_false hneg]
    twp_pures
    by_cases hlarge : (scale : ℤ) < v
    · rw [decide_eq_true hlarge]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp [clamp, hneg, hlarge]
    · rw [decide_eq_false hlarge]
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp [clamp, hneg, hlarge]

/-- Symbolic execution of sampling, deterministic evaluation, clamping, and flipping. -/
theorem twp_approximateFactory (E : CoPset) (p : unitInterval) (coin evaluate : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (trials scale : ℕ) [NeZero trials] [NeZero scale] (f : ℤ → ℤ)
    (hevaluate : ∀ k : Fin (trials + 1),
      ⊢ tglWp E pl(&evaluate.fst #int (scale : ℤ)
        #int ((scale : ℤ) * (k : ℕ) / trials))
        (fun v : Val rT => iprop(⌜v = Val.int (f ((scale : ℤ) * (k : ℕ) / trials))⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p trials scale f) -∗
      tglWp E pl(&Occil.FactoryExtra.approximateFactory &coin.fst #int (trials : ℤ)
        #int (scale : ℤ) &evaluate.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 5 twp_pure
  twp_pures
  simp only [nonpositive_test, Bool.false_or]
  twp_pure
  simp only [binomial_open, binomial_close,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.binomial &coin.fst #int (trials : ℤ))
  isimp only [← expectation p trials scale f F] at Hcredit
  iapply ((Binomial.binomial_distSpec E p coin hcoin trials).wp
    (countCredit trials scale f F) (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  by_cases hk : k ≤ trials
  · isimp only [countCredit, ite_eq_left hk] at Hcredit
    twp_pures
    twp_bind pl(&evaluate.fst #int (scale : ℤ) #int ((scale : ℤ) * k / trials))
    iapply tglWp_wand
    isplitl []
    · iapply hevaluate ⟨k, Nat.lt_succ_of_le hk⟩
    iintro %v %hv
    subst v
    twp_pure
    twp_bind pl(if #int (f ((scale : ℤ) * k / trials)) < #0 then #0 else
      if #int (scale : ℤ) < #int (f ((scale : ℤ) * k / trials)) then #int (scale : ℤ)
      else #int (f ((scale : ℤ) * k / trials)))
    iapply tglWp_wand
    isplitl []
    · iapply twp_clamp
    iintro %v %hv
    subst v
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    isimp only [componentBias] at Hcredit
    iapply (RationalCoin.twp_rationalCoin E (clamp scale (f ((scale : ℤ) * k / trials)))
      scale (clamp_nonneg ..)
      (Int.natCast_pos.mpr (NeZero.pos scale)) (clamp_le ..) F) $$ Hcredit
  · isimp only [countCredit, ite_eq_right hk] at Hcredit
    ihave %hbad := ErrorCredit.valid $$ Hcredit
    exact (not_lt_of_ge le_top hbad).elim

/-- The exact clamped plug-in law, for positive trial count and scale. -/
theorem approximateFactory_distSpec (E : CoPset) (p : unitInterval) (coin evaluate : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (trials scale : ℕ) [NeZero trials] [NeZero scale] (f : ℤ → ℤ)
    (hevaluate : ∀ k : Fin (trials + 1),
      ⊢ tglWp E pl(&evaluate.fst #int (scale : ℤ)
        #int ((scale : ℤ) * (k : ℕ) / trials))
        (fun v : Val rT => iprop(⌜v = Val.int (f ((scale : ℤ) * (k : ℕ) / trials))⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.approximateFactory &coin.fst
      #int (trials : ℤ) #int (scale : ℤ) &evaluate.fst #())
      (law p trials scale f) Val.bool where
  spec F _ := wand_entails
    (twp_approximateFactory E p coin evaluate hcoin trials scale f hevaluate F)

end specification

end

end SampLib.ApproximateFactory
