import SampLib.Discrete.PoissonOne
import SampLib.Uniform.RationalCoin
import SampLib.Common.Laws.Binomial
import SampLib.Common.Laws.PoissonThinning

/-! # Rational-rate Poisson sampling

Whole unit rates add independent Poisson counts. The fractional rate independently
thins one further count. Both branches preserve the same Poisson expectation.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.PoissonRational

noncomputable section

def rate (x y : ℕ) : ℝ≥0 := (x : ℝ≥0) / y

def bias (x y : ℕ) (hy : 0 < y) (hxy : x ≤ y) : unitInterval :=
  RationalCoin.bias x y (Int.natCast_nonneg _) (Int.natCast_pos.mpr hy)
    (Int.ofNat_le.mpr hxy)

section mathematics

open MeasureTheory

theorem rate_split (x y : ℕ) (hy : 0 < y) (hxy : y ≤ x) :
    rate x y = 1 + rate (x - y) y := by
  unfold rate
  have hy' : (y : ℝ≥0) ≠ 0 := by exact_mod_cast hy.ne'
  conv_lhs => rw [← Nat.add_sub_of_le hxy]
  rw [Nat.cast_add, add_div, div_self hy']

theorem bias_rate (x y : ℕ) (hy : 0 < y) (hxy : x ≤ y) :
    unitInterval.toNNReal (bias x y hy hxy) = rate x y := by
  apply NNReal.coe_injective
  simp [bias, rate, RationalCoin.bias]

def credit (x y total : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ k, F (total + k) ∂ProbabilityTheory.poissonMeasure (rate x y)

@[simp] theorem credit_zero (y total : ℕ) (F : ℕ → ℝ≥0∞) :
    credit 0 y total F = F total := by
  simp [credit, rate, Distributions.poissonMeasure_zero]

def drawCredit (x y total : ℕ) (hy : 0 < y) (F : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  if h : y ≤ x then credit (x - y) y (total + n) F
  else ∫⁻ k, F (total + k)
    ∂Binomial.law (bias x y hy (Nat.le_of_lt (Nat.lt_of_not_ge h))) n

/-- Additivity and thinning identify both branches with the requested remaining rate. -/
theorem expectation (x y total : ℕ) (hy : 0 < y) (F : ℕ → ℝ≥0∞) :
    (∫⁻ n, drawCredit x y total hy F n ∂ProbabilityTheory.poissonMeasure 1) =
      credit x y total F := by
  by_cases hxy : y ≤ x
  · simp only [drawCredit, dite_eq_left hxy, credit, Nat.add_assoc]
    simpa only [Nat.add_assoc, ← rate_split x y hy hxy] using
      Distributions.lintegral_poisson_add 1 (rate (x - y) y) (fun z => F (total + z))
  · simp only [drawCredit, dite_eq_right hxy]
    simp_rw [Binomial.law_eq_binomial]
    rw [← Measure.lintegral_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable,
      Distributions.poissonMeasure_bind_binomial, one_mul, bias_rate]
    rfl

private theorem remainder_lt (x y : ℕ) (hy : 0 < y) (hxy : y ≤ x) : x - y < x := by
  omega

private theorem sub_cast (x y : ℕ) (hxy : y ≤ x) :
    (x : ℤ) - y = ((x - y : ℕ) : ℤ) := by omega

private theorem positive_test (y : ℕ) (hy : 0 < y) :
    decide ((y : ℤ) ≤ 0) = false := decide_eq_false (by omega)

private theorem le_test (x y : ℕ) :
    decide ((y : ℤ) ≤ x) = decide (y ≤ x) := by simp

end mathematics

private def callback {rT : Type _} (x y : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin #int (x : ℤ) #int (y : ℤ)), .lam (by is_lc), by is_lc⟩

theorem poissonRational_lc {rT : Type _} :
    (Occil.poissonRational : Exp rT).IsLocallyClosed := by is_lc

theorem poissonRational_fv {rT : Type _} : (Occil.poissonRational : Exp rT).fv = ∅ := by
  simp [Occil.poissonRational, Occil.binomial, PoissonOne.poissonOne_fv,
    RationalCoin.rationalCoin_fv, Exp.fv]

@[simp] theorem poissonRational_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.poissonRational = Occil.poissonRational :=
  (Exp.open_lc k e _ poissonRational_lc).symm

@[simp] theorem poissonRational_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.poissonRational : Exp rT) = Occil.poissonRational :=
  Exp.closeRec_fresh x _ k (by simp [poissonRational_fv])

private def loop {rT : Type _} (y : ℕ) : Exp rT := pl%
  rec draw remaining total :=
    if #int (y : ℤ) <= remaining then
      draw (remaining - #int (y : ℤ)) (total + &Occil.poissonOne #())
    else if remaining = #0 then total else
      total + &Occil.binomial (fun u, &Occil.rationalCoin remaining #int (y : ℤ))
        (&Occil.poissonOne #())

private theorem binomial_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.binomial = Occil.binomial :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem binomial_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.binomial : Exp rT) = Occil.binomial :=
  Exp.closeRec_fresh x _ k (by simp [Occil.binomial, Exp.fv])

attribute [local simp] binomial_open binomial_close

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem callback_distSpec (E : CoPset) (x y : ℕ) (hy : 0 < y) (hxy : x ≤ y) :
    IsDistSpec (GF := GF) E pl(&(callback x y).fst #())
      (RealCoin.law (bias x y hy hxy)) Val.bool where
  spec F hF := by
    iintro Hcredit
    isimp only [bias] at Hcredit
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    iapply (RationalCoin.rationalCoin_distSpec E x y (Int.natCast_nonneg _)
      (Int.natCast_pos.mpr hy) (Int.ofNat_le.mpr hxy)).spec F hF $$ Hcredit

private theorem twp_loop (E : CoPset) (x y total : ℕ) (hy : 0 < y)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit x y total F) -∗ tglWp E pl(&(loop y) #int (x : ℤ) #int (total : ℤ))
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction x using Nat.strong_induction_on generalizing total with
  | h x IH =>
    iintro Hcredit
    iterate 4 twp_pure
    rw [le_test]
    by_cases hxy : y ≤ x
    · rw [decide_eq_true hxy]
      twp_pure
      simp only [PoissonOne.poissonOne_openRec, PoissonOne.poissonOne_closeRec,
        RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
      twp_bind pl(&Occil.poissonOne #())
      isimp only [← expectation x y total hy F] at Hcredit
      iapply ((PoissonOne.poissonOne_distSpec E).wp (drawCredit x y total hy F)
        (measurable_of_countable _) _) $$ Hcredit
      iintro %n Hcredit
      isimp only [drawCredit, dite_eq_left hxy] at Hcredit
      iterate 2 twp_pure
      rw [sub_cast x y hxy]
      isimp [Exp.ofVal, Exp.close, Exp.closeRec]
      have h := IH (x - y) (remainder_lt x y hy hxy) (total + n)
      simp [loop, Exp.close, Exp.closeRec] at h
      iapply h $$ Hcredit
    · rw [decide_eq_false hxy]
      twp_pures
      rw [int_beq]
      by_cases hx : x = 0
      · subst x
        rw [Nat.cast_zero, beq_self_eq_true]
        twp_pures
        twp_value
        imodintro
        iexists total
        isimp only [credit_zero] at Hcredit
        iframe Hcredit
        itrivial
      · rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hx)]
        twp_pure
        simp only [PoissonOne.poissonOne_openRec, PoissonOne.poissonOne_closeRec,
          RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec,
          binomial_open, binomial_close]
        twp_bind pl(&Occil.poissonOne #())
        isimp only [← expectation x y total hy F] at Hcredit
        iapply ((PoissonOne.poissonOne_distSpec E).wp (drawCredit x y total hy F)
          (measurable_of_countable _) _) $$ Hcredit
        iintro %n Hcredit
        isimp only [drawCredit, dite_eq_right hxy] at Hcredit
        isimp only [Exp.ofVal, RationalCoin.rationalCoin_openRec,
          RationalCoin.rationalCoin_closeRec, binomial_open, binomial_close]
        twp_bind pl(&Occil.binomial &(callback x y).fst #int (n : ℤ))
        iapply ((Binomial.binomial_distSpec E
          (bias x y hy (Nat.le_of_lt (Nat.lt_of_not_ge hxy))) (callback x y)
          (callback_distSpec E x y hy (Nat.le_of_lt (Nat.lt_of_not_ge hxy))) n).wp
          (fun k => F (total + k)) (measurable_of_countable _) _) $$ Hcredit
        iintro %k Hcredit
        twp_pures
        rw [← Nat.cast_add]
        twp_value
        imodintro
        iexists total + k
        iframe Hcredit
        itrivial

theorem twp_poissonRational (E : CoPset) (x y : ℕ) (hy : 0 < y) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit x y 0 F) -∗ tglWp E pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  twp_pures
  simp only [positive_test y hy, Bool.or_false]
  twp_pures
  rw [int_beq]
  by_cases hx : x = 0
  · subst x
    rw [Nat.cast_zero, beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  · rw [beq_eq_false_iff_ne.mpr (by exact_mod_cast hx)]
    iterate 2 twp_pure
    isimp [Exp.ofVal, Exp.close, Exp.closeRec]
    have h := twp_loop (rT := rT) (GF := GF) E x y 0 hy F
    simp [loop, Exp.close, Exp.closeRec] at h
    iapply h $$ Hcredit

/-- Every nonnegative rational rate, including zero, has its canonical Poisson law. -/
theorem poissonRational_distSpec (E : CoPset) (x y : ℕ) (hy : 0 < y) :
    IsDistSpec (GF := GF) E pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
      (ProbabilityTheory.poissonMeasure (rate x y)) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := by
    simpa only [credit, Nat.zero_add] using wand_entails (twp_poissonRational E x y hy F)

end specification

end

end SampLib.PoissonRational
