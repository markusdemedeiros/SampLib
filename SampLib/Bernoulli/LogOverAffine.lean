import SampLib.Bernoulli.ReciprocalAffine
import SampLib.Bernoulli.PLogInverse

/-! # The logarithmic reciprocal-affine factory

A reciprocal-affine coin feeds the geometric reciprocal-count construction.
The existing logarithmic identity evaluates its bias as `log(c+p)/(c+p)`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LogOverAffine

noncomputable section

/-- Bias of the inner reciprocal-affine coin. -/
def reciprocalBias (p : unitInterval) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) : unitInterval :=
  ReciprocalAffine.bias p a b b (lt_of_lt_of_le hb hab) hab

private theorem reciprocal_pos (p : unitInterval) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    0 < (reciprocalBias p a b hb hab : ℝ) := by
  change 0 < (b : ℝ) / ((a : ℝ) + b * (p : ℝ))
  apply div_pos (by exact_mod_cast hb)
  exact add_pos_of_pos_of_nonneg (by exact_mod_cast lt_of_lt_of_le hb hab)
    (mul_nonneg (Nat.cast_nonneg b) p.2.1)

/-- The output bias, including zero when `a=b` and `p=0`. -/
def bias (p : unitInterval) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) : unitInterval :=
  PLogInverse.bias (reciprocalBias p a b hb hab) (reciprocal_pos p a b hb hab)

/-- The reciprocal substitution turns `q log(1/q)` into `log(c+p)/(c+p)`. -/
theorem bias_coe (p : unitInterval) (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    (bias p a b hb hab : ℝ) = Real.log ((a : ℝ) / b + (p : ℝ)) /
      ((a : ℝ) / b + (p : ℝ)) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hden : 0 < (a : ℝ) + b * (p : ℝ) :=
    add_pos_of_pos_of_nonneg (by exact_mod_cast lt_of_lt_of_le hb hab)
      (mul_nonneg (Nat.cast_nonneg b) p.2.1)
  have hrec : (b : ℝ) / ((a : ℝ) + b * (p : ℝ)) =
      1 / ((a : ℝ) / b + (p : ℝ)) := by
    field_simp
  change (b : ℝ) / ((a : ℝ) + b * (p : ℝ)) *
    Real.log (1 / ((b : ℝ) / ((a : ℝ) + b * (p : ℝ)))) = _
  rw [hrec, one_div_one_div]
  ring

private def reciprocalCoin {rT : Type _} (coin : Val rT) (a b : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.reciprocalAffine &coin.fst #int (a : ℤ)
    #int (b : ℤ) #1 #1 #()), .lam (by is_lc), by is_lc⟩

private theorem reciprocal_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.reciprocalAffine = Occil.FactoryExtra.reciprocalAffine :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem reciprocal_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.reciprocalAffine : Exp rT) =
      Occil.FactoryExtra.reciprocalAffine :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.reciprocalAffine, Exp.fv, UniformInt.uniformInt_fv])

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem valid_test (a b : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    Bool.or (decide ((b : ℤ) ≤ 0)) (decide ((a : ℤ) < b)) = false := by
  have hb' : decide ((b : ℤ) ≤ 0) = false :=
    decide_eq_false (by exact_mod_cast Nat.not_le.mpr hb)
  have hab' : decide ((a : ℤ) < b) = false :=
    decide_eq_false (by exact_mod_cast Nat.not_lt.mpr hab)
  rw [hb', hab']

private theorem zero_credit (F : Bool → ℝ≥0∞) :
    RealCoin.credit (PLogInverse.countBias 0) F = F false := by
  simp [RealCoin.credit, RealCoin.pmf, PLogInverse.countBias]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem reciprocal_spec (E : CoPset) (p : unitInterval) (a b : ℕ)
    (hb : 0 < b) (hab : b ≤ a) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(reciprocalCoin coin a b).fst #())
      (RealCoin.law (reciprocalBias p a b hb hab)) Val.bool where
  spec F hF := by
    have hrec := ReciprocalAffine.reciprocalAffine_distSpec (GF := GF) E p a b 1 1
      (lt_of_lt_of_le hb hab) hb zero_lt_one (by simpa using hab) coin hcoin
    simp only [Nat.mul_one, Nat.one_mul] at hrec
    iintro Hcredit
    twp_pure
    simp only [reciprocal_open]
    iapply hrec.spec F hF
    isimp only [reciprocalBias] at Hcredit
    iexact Hcredit

/-- Execute the geometric reciprocal-count construction with the verified inner coin. -/
theorem twp_logOverAffine (E : CoPset) (p : unitInterval) (a b : ℕ)
    (hb : 0 < b) (hab : b ≤ a) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂RealCoin.law (bias p a b hb hab)) -∗
      tglWp E pl(&Occil.FactoryExtra.logOverAffine &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ x : Bool, ⌜v = Val.bool x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  iterate 4 twp_pure
  twp_pures
  rw [valid_test a b hb hab]
  twp_pure
  simp only [geometric_open, geometric_close, reciprocal_open, reciprocal_close,
    RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
  twp_bind pl(&Occil.geometric &(reciprocalCoin coin a b).fst #())
  isimp only [RealCoin.lintegral_law, bias,
    ← PLogInverse.expectation_preservation (reciprocalBias p a b hb hab)
      (reciprocal_pos p a b hb hab) F] at Hcredit
  iapply ((Geometric.geometric_distSpec E (reciprocalBias p a b hb hab)
    (reciprocal_pos p a b hb hab) (reciprocalCoin coin a b)
    (reciprocal_spec E p a b hb hab coin hcoin)).wp
    (fun n => RealCoin.credit (PLogInverse.countBias n) F) (measurable_of_countable _) _)
    $$ Hcredit
  iintro %n Hcredit
  cases n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [zero_credit] at Hcredit
    iframe Hcredit
    itrivial
  | succ n =>
    twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    iterate 2 twp_pure
    rw [Nat.cast_add_one]
    isimp only [PLogInverse.countBias] at Hcredit
    iapply (RationalCoin.twp_rationalCoin E 1 (n + 1) _ _ _ F) $$ Hcredit

/-- Exact logarithmic-affine bias for every rational `a/b≥1` and every input coin. -/
theorem logOverAffine_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ)
    (hb : 0 < b) (hab : b ≤ a) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.logOverAffine
      &coin.fst #int (a : ℤ) #int (b : ℤ) #()) (RealCoin.law (bias p a b hb hab)) Val.bool where
  spec F _ := wand_entails (twp_logOverAffine E p a b hb hab coin hcoin F)

end specification

end

end SampLib.LogOverAffine
