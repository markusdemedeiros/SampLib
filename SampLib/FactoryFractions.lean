import SampLib.Templates
import Samplers.Bernoulli.Arithmetic
import SampLib.Syntax.ClosedExp

/-! # Exact fraction arithmetic for the factory engines

The source normalizes every rational pair by Euclid's algorithm. The operational
rules retain its exact integer representation; algebraic value lemmas can then
be used without expanding the normalization loop in sampler proofs.
-/

open ProbLang

namespace SampLib.FactoryFractions

/-- The canonical rational representation used by the source terms. -/
def encode {rT : Type _} (q : ℚ) : Val rT :=
  .pair (.int q.num) (.int q.den)

/-- An unreduced source pair with a positive denominator. -/
structure Fraction where
  numerator : ℤ
  denominator : ℕ
  positive : 0 < denominator

def Fraction.value (a : Fraction) : ℚ := mkRat a.numerator a.denominator

def Fraction.encode {rT : Type _} (a : Fraction) : Val rT :=
  .pair (.int a.numerator) (.int a.denominator)

/-- The result of source normalization. -/
def Fraction.ofRat (q : ℚ) : Fraction := ⟨q.num, q.den, q.den_pos⟩

@[simp] theorem Fraction.value_ofRat (q : ℚ) : (Fraction.ofRat q).value = q := by
  exact Rat.mkRat_self q

@[simp] theorem Fraction.encode_ofRat {rT : Type _} (q : ℚ) :
    ((Fraction.ofRat q).encode : Val rT) = FactoryFractions.encode q := rfl

private theorem add_value (a b : Fraction) :
    mkRat (a.numerator * b.denominator + b.numerator * a.denominator)
      (a.denominator * b.denominator) = a.value + b.value := by
  exact (Rat.mkRat_add_mkRat a.numerator b.numerator
    (Nat.ne_of_gt a.positive) (Nat.ne_of_gt b.positive)).symm

private theorem subtract_value (a b : Fraction) :
    mkRat (a.numerator * b.denominator - b.numerator * a.denominator)
      (a.denominator * b.denominator) = a.value - b.value := by
  simp only [Fraction.value, sub_eq_add_neg, Rat.neg_mkRat]
  simpa only [neg_mul] using
    (Rat.mkRat_add_mkRat a.numerator (-b.numerator)
      (Nat.ne_of_gt a.positive) (Nat.ne_of_gt b.positive)).symm

/-- The encoded rational pair has its literal quotient as mathematical value. -/
theorem Fraction.cast_value (a : Fraction) :
    (a.value : ℝ) = (a.numerator : ℝ) / (a.denominator : ℝ) :=
  Rat.cast_mkRat_of_ne_zero a.numerator (by exact_mod_cast (Nat.ne_of_gt a.positive))

private theorem multiply_value (a b : Fraction) :
    mkRat (a.numerator * b.numerator) (a.denominator * b.denominator) = a.value * b.value :=
  (Rat.mkRat_mul_mkRat a.numerator b.numerator a.denominator b.denominator).symm

private theorem divide_value (a b : Fraction) (hb : 0 < b.numerator) :
    mkRat (a.numerator * b.denominator) (a.denominator * b.numerator.toNat) =
      a.value / b.value := by
  have ha : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt a.positive)
  have hd : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt b.positive)
  have hn : (b.numerator : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc : (b.numerator.toNat : ℚ) = b.numerator := by
    exact_mod_cast Int.toNat_of_nonneg hb.le
  simp only [Fraction.value, Rat.mkRat_eq_div, Nat.cast_mul, Int.cast_mul,
    Int.cast_natCast, hc]
  field_simp

private theorem encode_mkRat {rT : Type _} (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    (encode (mkRat n d) : Val rT) =
      .pair (.int (n / (Nat.gcd n.natAbs d : ℤ)))
        (.int ((d : ℤ) / (Nat.gcd n.natAbs d : ℤ))) := by
  simp only [encode, mkRat, dite_eq_right hd, Rat.num_normalize, Rat.den_normalize,
    Int.natCast_ediv]

instance fraction_closed {rT : Type _} :
    ClosedExp (Occil.FactoryExtra.fraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.fraction, Exp.fv]

instance addFraction_closed {rT : Type _} :
    ClosedExp (Occil.FactoryExtra.addFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.addFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

instance subtractFraction_closed {rT : Type _} :
    ClosedExp (Occil.FactoryExtra.subtractFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.subtractFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private def gcdLoop {rT : Type _} : Exp rT := pl%
  rec reduce a b := if b = #0 then a else reduce b (a % b)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_gcdLoop (E : CoPset) (a b : ℕ) :
    ⊢ tglWp E pl(&(gcdLoop (rT := rT)) #int (a : ℤ) #int (b : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (Nat.gcd a b : ℤ)⌝)) := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b IH =>
    by_cases hb : b = 0
    · subst b
      twp_pures
      twp_value
      imodintro
      ipureintro
      simp
    · twp_pures
      have htest : ((b : ℤ) == 0) = false := by simp [hb]
      ieval (change _ ⊢ tglWp E (Exp.cond (Exp.lit (.bool ((b : ℤ) == 0))) _ _) _)
      rw [htest]
      iterate 2 twp_pure
      have hrec := IH (a % b) (Nat.mod_lt a (Nat.pos_of_ne_zero hb)) b
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a] at hrec
      simp [gcdLoop, Exp.close, Exp.closeRec] at hrec
      iapply hrec

private theorem twp_absolute (E : CoPset) (n : ℤ) :
    ⊢ tglWp E pl(if #bool (decide (n < 0)) then -#int n else #int n)
      (fun v : Val rT => iprop(⌜v = Val.int (n.natAbs : ℤ)⌝)) := by
  by_cases hn : n < 0
  · rw [decide_eq_true hn]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [abs_of_neg hn]
  · rw [decide_eq_false hn]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [abs_of_nonneg (le_of_not_gt hn)]

/-- Canonicalize a signed numerator over a positive denominator. -/
theorem twp_fraction (E : CoPset) (n : ℤ) (d : ℕ) (hd : 0 < d) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.fraction #int n #int (d : ℤ))
      (fun v : Val rT => iprop(⌜v = encode (mkRat n d)⌝)) := by
  twp_pures
  have hd0 : ((d : ℤ) == 0) = false := by simp [Nat.ne_of_gt hd]
  ieval (change _ ⊢ tglWp E (Exp.cond (Exp.lit (.bool ((d : ℤ) == 0))) _ _) _)
  rw [hd0]
  twp_pures
  simp -failIfUnchanged only [mul_one]
  twp_bind pl(if #bool (decide (n < 0)) then -#int n else #int n)
  iapply tglWp_wand
  isplitl []
  · iapply twp_absolute E n
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  twp_bind pl(&(gcdLoop (rT := rT)) #int (n.natAbs : ℤ) #int (d : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_gcdLoop E n.natAbs d
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  exact (encode_mkRat n d (Nat.ne_of_gt hd)).symm

/-- Add unreduced pairs and return their canonical rational sum. -/
theorem twp_addFraction (E : CoPset) (a b : Fraction) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.addFraction &a.encode.fst &b.encode.fst)
      (fun v : Val rT => iprop(⌜v = encode (a.value + b.value)⌝)) := by
  iterate 12 twp_pure
  simp only [← Nat.cast_mul, ClosedExp.closeRec, ClosedExp.openRec, Exp.ofVal]
  rw [← add_value a b]
  iapply twp_fraction E _ _ (Nat.mul_pos a.positive b.positive)

/-- Subtract unreduced pairs and return their canonical rational difference. -/
theorem twp_subtractFraction (E : CoPset) (a b : Fraction) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.subtractFraction &a.encode.fst &b.encode.fst)
      (fun v : Val rT => iprop(⌜v = encode (a.value - b.value)⌝)) := by
  iterate 12 twp_pure
  simp only [← Nat.cast_mul, ClosedExp.closeRec, ClosedExp.openRec, Exp.ofVal]
  rw [← subtract_value a b]
  iapply twp_fraction E _ _ (Nat.mul_pos a.positive b.positive)

/-- Multiply unreduced pairs and return their canonical rational product. -/
theorem twp_multiplyFraction (E : CoPset) (a b : Fraction) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.multiplyFraction &a.encode.fst &b.encode.fst)
      (fun v : Val rT => iprop(⌜v = encode (a.value * b.value)⌝)) := by
  iterate 8 twp_pure
  simp only [← Nat.cast_mul, ClosedExp.closeRec, ClosedExp.openRec, Exp.ofVal]
  rw [← multiply_value a b]
  iapply twp_fraction E _ _ (Nat.mul_pos a.positive b.positive)

/-- Divide by a positive rational pair, as used for unresolved interval widths. -/
theorem twp_divideFraction (E : CoPset) (a b : Fraction) (hb : 0 < b.numerator) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.divideFraction &a.encode.fst &b.encode.fst)
      (fun v : Val rT => iprop(⌜v = encode (a.value / b.value)⌝)) := by
  have hden : 0 < b.numerator.toNat := by omega
  have h := twp_fraction (rT := rT) (GF := GF) E (a.numerator * b.denominator)
    (a.denominator * b.numerator.toNat) (Nat.mul_pos a.positive hden)
  rw [divide_value a b hb] at h
  simp only [Nat.cast_mul, Int.toNat_of_nonneg hb.le] at h
  iterate 8 twp_pure
  simp only [ClosedExp.closeRec, ClosedExp.openRec, Exp.ofVal]
  iapply h

end specification

end SampLib.FactoryFractions
