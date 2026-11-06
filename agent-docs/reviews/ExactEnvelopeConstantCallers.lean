import SampLib.Samplers.EnvelopeFactory
import SampLib.Distributions.BernoulliEndpoints

open ProbLang Finset Filter
open scoped ENNReal Topology

namespace ExactEnvelopeConstantCallers

noncomputable section

open SampLib SampLib.EnvelopeFactory FactoryFractions

private theorem reverse_sum (degree : ℕ → ℕ) (hg : ∀ t, degree t < degree (t + 1))
    (t : ℕ) (k : Fin (degree (t + 1) + 1)) :
    (∑ j : Fin (degree t + 1),
      ReverseBinomial.coefficient (degree t) (degree (t + 1)) k j) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    ReverseBinomial.coefficient (degree t) (degree (t + 1)) k j)]
  exact ReverseBinomial.coefficient_sum_degree _ _ _ (hg t).le (Nat.le_of_lt_succ k.isLt)

def constantCoefficients (degree : ℕ → ℕ) (h0 : degree 0 = 0)
    (hg : ∀ t, degree t < degree (t + 1)) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Coefficients where
  degree := degree
  initial_degree := h0
  grows := hg
  lower t _ := if t = 0 then 0 else q
  upper t _ := if t = 0 then 1 else q
  bounds t _ := by
    by_cases ht : t = 0
    · simp only [ht, ite_true]
      norm_num
    · simp only [ht, ite_false]
      exact ⟨hq0, le_rfl, hq1⟩
  lower_initial _ := by simp
  upper_initial _ := by simp
  lower_consistent t k := by
    by_cases ht : t = 0
    · simpa only [ht, ite_true, Nat.succ_ne_zero, ite_false, mul_zero, sum_const_zero] using hq0
    · simpa only [ht, ite_false, Nat.succ_ne_zero, ← sum_mul,
        reverse_sum degree hg t k, one_mul] using (le_refl q)
  upper_consistent t k := by
    by_cases ht : t = 0
    · subst t
      simpa only [ite_true, Nat.succ_ne_zero, ite_false, mul_one,
        reverse_sum degree hg 0 k] using hq1
    · simpa only [ht, ite_false, Nat.succ_ne_zero, ← sum_mul,
        reverse_sum degree hg t k, one_mul] using (le_refl q)

private theorem constant_means (degree : ℕ → ℕ) (h0 : degree 0 = 0)
    (hg : ∀ t, degree t < degree (t + 1)) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (t : ℕ) (ht : t ≠ 0) (p : unitInterval) :
    (constantCoefficients degree h0 hg q hq0 hq1).lowerMean t p = (q : ℝ) ∧
      (constantCoefficients degree h0 hg q hq0 hq1).upperMean t p = (q : ℝ) := by
  change (∑ k : Fin (degree t + 1), bernstein (degree t) k p *
      ((if t = 0 then 0 else q : ℚ) : ℝ)) = _ ∧
    (∑ k : Fin (degree t + 1), bernstein (degree t) k p *
      ((if t = 0 then 1 else q : ℚ) : ℝ)) = _
  simp only [ht, ite_false]
  constructor <;> rw [← sum_mul, bernstein.probability, one_mul]

def constantParameters (degree : ℕ → ℕ) (h0 : degree 0 = 0)
    (hg : ∀ t, degree t < degree (t + 1)) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Parameters where
  toCoefficients := constantCoefficients degree h0 hg q hq0 hq1
  target _ := ⟨(q : ℝ), by exact_mod_cast hq0, by exact_mod_cast hq1⟩
  lower_converges p := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (constant_means degree h0 hg q hq0 hq1 t ht.ne' p).1.symm
  upper_converges p := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (constant_means degree h0 hg q hq0 hq1 t ht.ne' p).2.symm

def realization (degree : ℕ → ℕ) (h0 : degree 0 = 0)
    (hg : ∀ t, degree t < degree (t + 1)) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (c : Fraction) (hc : c.value = q) :
    (constantParameters degree h0 hg q hq0 hq1).toCoefficients.Realization where
  raw _ _ _ := c
  value t ht _ _ := by
    simp only [constantParameters, constantCoefficients, ht.ne', ite_false, ite_self]
    exact hc

def bounds {rT : Type} (c : Fraction) : Val rT :=
  ⟨.lam (.lam (.pair c.encode.fst c.encode.fst)), .lam (by is_lc), by is_lc⟩

def coin {rT : Type} (b : Bool) : Val rT :=
  ⟨.lam (Val.bool b).fst, .lam (by is_lc), by is_lc⟩

def nextTwo {rT : Type} : Val rT :=
  ⟨.lam (.binop .plus (.bvar 0) pl(#2)), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem bounds_spec (E : CoPset) (degree : ℕ → ℕ) (h0 : degree 0 = 0)
    (hg : ∀ t, degree t < degree (t + 1)) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (c : Fraction) (hc : c.value = q) :
    BoundsSpec (GF := GF) E (constantParameters degree h0 hg q hq0 hq1).toCoefficients
      (realization degree h0 hg q hq0 hq1 c hc) (bounds c : Val rT) := by
  intro t _ k
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

omit [ProbLangDist.IsUniformInt rT] in
private theorem coin_spec (E : CoPset) (b : Bool) :
    IsDistSpec (GF := GF) E pl(&(coin b : Val rT).fst #())
      (RealCoin.law (if b then 1 else 0)) Val.bool where
  spec F _ := by
    cases b
    · simp only [Bool.false_eq_true, ite_false, RealCoin.lintegral_law, RealCoin.credit_zero]
      iintro Hcredit
      twp_pures
      twp_value
      imodintro
      iexists false
      iframe Hcredit
      itrivial
    · simp only [ite_true, RealCoin.lintegral_law, RealCoin.credit_one]
      iintro Hcredit
      twp_pures
      twp_value
      imodintro
      iexists true
      iframe Hcredit
      itrivial

omit [ProbLangDist.IsUniformInt rT] in
private theorem nextTwo_spec (E : CoPset) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    NextSpec (GF := GF) E
      (constantParameters (fun t => 2 * t) (by omega) (by intro t; omega) q hq0 hq1).toCoefficients
      (nextTwo : Val rT) := by
  intro t
  twp_pures
  twp_value
  imodintro
  ipureintro
  congr 1

private def third : Fraction := ⟨2, 6, by decide⟩
private theorem third_value : third.value = (1 : ℚ) / 3 := by
  norm_num [third, Fraction.value, Rat.mkRat_eq_div]

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &(coin false : Val rT).fst &(bounds third : Val rT).fst &(nextTwo : Val rT).fst #())
      (RealCoin.law ((constantParameters (fun t => 2 * t) (by omega) (by intro t; omega)
        (1 / 3) (by norm_num) (by norm_num)).target 0)) Val.bool := by
  exact envelopeFactoryDegrees_distSpec E _
    (realization _ _ _ _ _ _ third third_value) 0 _ _ _ (coin_spec E false)
    (bounds_spec E _ _ _ _ _ _ third third_value) (nextTwo_spec E _ _ _)

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactory
      &(coin true : Val rT).fst &(bounds (Fraction.ofRat 0) : Val rT).fst #())
      (RealCoin.law 0) Val.bool := by
  have h := envelopeFactory_distSpec (GF := GF) E
    (constantParameters (fun t => t) rfl (by intro t; omega) 0 (by norm_num) (by norm_num))
    (realization _ _ _ _ _ _ (.ofRat 0) (by simp)) (fun _ => rfl) 1 _ _ (coin_spec E true)
    (bounds_spec E _ _ _ _ _ _ (.ofRat 0) (by simp))
  convert h using 1
  congr 2
  apply Subtype.ext
  norm_num [constantParameters]

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactory
      &(coin false : Val rT).fst &(bounds (Fraction.ofRat 1) : Val rT).fst #())
      (RealCoin.law 1) Val.bool := by
  have h := envelopeFactory_distSpec (GF := GF) E
    (constantParameters (fun t => t) rfl (by intro t; omega) 1 (by norm_num) (by norm_num))
    (realization _ _ _ _ _ _ (.ofRat 1) (by simp)) (fun _ => rfl) 0 _ _ (coin_spec E false)
    (bounds_spec E _ _ _ _ _ _ (.ofRat 1) (by simp))
  convert h using 1
  congr 2
  apply Subtype.ext
  norm_num [constantParameters]

end specification

#print axioms constantParameters
#print axioms realization

end

end ExactEnvelopeConstantCallers
