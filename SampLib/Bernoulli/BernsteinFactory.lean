import SampLib.Core.ListEncoding
import SampLib.Common.Laws.Binomial
import SampLib.Uniform.RationalCoin
import Samplers.Bernoulli.Combinators

/-! # Bernstein polynomial coins

A binomial count chooses a rational coefficient. The resulting law is the
Bernstein mixture of those coefficient coins.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.BernsteinFactory

noncomputable section

/-- Rational coefficients in the unit interval. -/
abbrev Coefficient := {q : ℤ × ℤ // 0 ≤ q.1 ∧ 0 < q.2 ∧ q.1 ≤ q.2}

def coefficientBias (q : Coefficient) : unitInterval :=
  RationalCoin.bias q.val.1 q.val.2 q.property.1 q.property.2.1 q.property.2.2

private def zeroCoefficient : Coefficient := ⟨(0, 1), by norm_num⟩

/-- Total lookup; its default is outside the binomial support. -/
def coefficient (qs : List Coefficient) (k : ℕ) : Coefficient :=
  qs[k]?.getD zeroCoefficient

section mathematics

open MeasureTheory Measure

/-- A binomial count cannot exceed the number of trials. -/
theorem binomial_support (p : unitInterval) (n : ℕ) :
    ∀ᵐ k ∂Binomial.law p n, k ≤ n := by
  induction n with
  | zero => simp [Binomial.law]
  | succ n IH =>
    rw [Binomial.law, ae_add_measure_iff]
    constructor
    · apply ae_smul_measure _ (RealCoin.pmf p true)
      apply (ae_map_iff (measurable_of_countable _).aemeasurable
        (Set.to_countable _).measurableSet).2
      exact IH.mono fun k hk => Nat.succ_le_succ hk
    · exact ae_smul_measure (IH.mono fun k hk => hk.trans (Nat.le_succ _)) _

/-- Mix the coefficient coins against the degree-`length-1` binomial law. -/
def law (p : unitInterval) (qs : List Coefficient) : Measure Bool :=
  (Binomial.law p (qs.length - 1)).bind
    (fun k => RealCoin.law (coefficientBias (coefficient qs k)))

instance (p : unitInterval) (qs : List Coefficient) : IsProbabilityMeasure (law p qs) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]

/-- The success probability is the Bernstein polynomial of the coefficient biases. -/
theorem success_probability (p : unitInterval) (qs : List Coefficient) :
    law p qs {true} = ∑ k ∈ Finset.range (qs.length - 1 + 1),
      ENNReal.ofReal (((qs.length - 1).choose k : ℝ) * (p : ℝ) ^ k *
        (1 - (p : ℝ)) ^ (qs.length - 1 - k)) *
      ENNReal.ofReal (coefficientBias (coefficient qs k) : ℝ) := by
  rw [law, Measure.bind_apply (measurableSet_singleton true)
    (measurable_of_countable _).aemeasurable]
  simpa [RealCoin.law, RealCoin.pmf] using
    Binomial.lintegral_eq_sum p (qs.length - 1)
      (fun k => ENNReal.ofReal (coefficientBias (coefficient qs k) : ℝ))

/-- Out-of-support counts receive impossible credit, so lookup needs no fallback. -/
def countCredit (qs : List Coefficient) (F : Bool → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < qs.length then RealCoin.credit (coefficientBias (coefficient qs k)) F else ∞

/-- Conditioning on the binomial count preserves the Bernstein expectation. -/
theorem expectation (p : unitInterval) (qs : List Coefficient) [NeZero qs.length]
    (F : Bool → ℝ≥0∞) :
    ∫⁻ k, countCredit qs F k ∂Binomial.law p (qs.length - 1) =
      ∫⁻ b, F b ∂law p qs := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable F).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [binomial_support p (qs.length - 1)] with k hk
  rw [countCredit, ite_eq_left (by have := NeZero.pos qs.length; omega),
    RealCoin.lintegral_law]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

private theorem binomial_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.binomial = Occil.binomial :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem binomial_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.binomial : Exp rT) = Occil.binomial :=
  Exp.closeRec_fresh x _ k (by simp [Occil.binomial, Exp.fv])

private theorem getAt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.getAt = Occil.getAt :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem getAt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.getAt : Exp rT) = Occil.getAt :=
  Exp.closeRec_fresh x _ k (by simp [Occil.getAt, Exp.fv])

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def encodeCoefficient (q : Coefficient) : Val rT := .pair (.int q.val.1) (.int q.val.2)

private theorem coefficient_get (qs : List Coefficient) (k : ℕ) (hk : k < qs.length) :
    coefficient qs k = qs.get ⟨k, hk⟩ := by
  simp [coefficient, List.getElem?_eq_getElem hk]

private theorem degree_cast (qs : List Coefficient) [NeZero qs.length] :
    (qs.length : ℤ) - 1 = ((qs.length - 1 : ℕ) : ℤ) := by
  have := NeZero.pos qs.length
  omega

/-- Symbolic execution: count trials, look up the coefficient, flip its coin. -/
theorem twp_bernsteinFactory (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (qs : List Coefficient) [NeZero qs.length] (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂law p qs) -∗
      tglWp E pl(&Occil.bernsteinFactory &coin.fst
        &(listVal (encodeCoefficient (rT := rT)) qs).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pure
  twp_pure
  twp_pure
  twp_bind pl(&Occil.length &(listVal (encodeCoefficient (rT := rT)) qs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length
  iintro %v %hv
  subst v
  twp_pures
  rw [degree_cast qs]
  simp only [binomial_openRec, binomial_closeRec, getAt_openRec, getAt_closeRec,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_pure
  twp_bind pl(&Occil.binomial &coin.fst #int ((qs.length - 1 : ℕ) : ℤ))
  isimp only [← expectation p qs F] at Hcredit
  iapply ((Binomial.binomial_distSpec E p coin hcoin (qs.length - 1)).wp
    (countCredit qs F) (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  by_cases hk : k < qs.length
  · isimp only [countCredit, ite_eq_left hk, coefficient_get qs k hk, coefficientBias] at Hcredit
    twp_pure
    twp_bind pl(&Occil.getAt &(listVal (encodeCoefficient (rT := rT)) qs).fst #int (k : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply (twp_getAt E (encodeCoefficient (rT := rT)) qs ⟨k, hk⟩)
    iintro %v %hv
    subst v
    simp only [encodeCoefficient]
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    twp_pure
    twp_pure
    simp only [Exp.ofVal]
    iapply (RationalCoin.twp_rationalCoin E (qs.get ⟨k, hk⟩).val.1
      (qs.get ⟨k, hk⟩).val.2 (qs.get ⟨k, hk⟩).property.1
      (qs.get ⟨k, hk⟩).property.2.1 (qs.get ⟨k, hk⟩).property.2.2 F) $$ Hcredit
  · isimp only [countCredit, ite_eq_right hk] at Hcredit
    ihave %hbad := ErrorCredit.valid $$ Hcredit
    exact (not_lt_of_ge le_top hbad).elim

/-- Typed Bernstein law, including degree zero and endpoint input coins. -/
theorem bernsteinFactory_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (qs : List Coefficient) [NeZero qs.length] :
    IsDistSpec (GF := GF) E pl(&Occil.bernsteinFactory &coin.fst
      &(listVal (encodeCoefficient (rT := rT)) qs).fst #()) (law p qs) Val.bool where
  spec F _ := wand_entails (twp_bernsteinFactory E p coin hcoin qs F)

end specification

end

end SampLib.BernsteinFactory
