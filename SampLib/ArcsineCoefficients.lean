import SampLib.FactoryChoose
import SampLib.FactoryIntegerPower
import SampLib.FactoryFractions
import SampLib.Distributions.ArcsineFactoryCoefficients

/-! # Exact coefficient evaluation for the arcsine factory -/

open ProbLang

namespace SampLib.ArcsineCoefficients

def index (n : ℕ) : ℕ := (n + 1) / 2

def factor (n : ℕ) : ℕ := if (n + 1) % 2 = 1 then n + 1 else n

private theorem factor_pos (n : ℕ) : 0 < factor n := by
  unfold factor
  split_ifs <;> omega

def raw (n : ℕ) : FactoryFractions.Fraction :=
  ⟨(index n).centralBinom, 4 ^ index n * factor n,
    Nat.mul_pos (by positivity) (factor_pos n)⟩

theorem raw_value (n : ℕ) : (raw n).value = ArcsineFactoryCoefficients.coefficient n := by
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have he : n = 2 * (n / 2) := by omega
    rw [he, ArcsineFactoryCoefficients.coefficient_even]
    have hi : (2 * (n / 2) + 1) / 2 = n / 2 := by omega
    have ho : (2 * (n / 2) + 1) % 2 = 1 := by omega
    simp [raw, index, factor, hi, ho, FactoryFractions.Fraction.value, Rat.mkRat_eq_div,
      ArcsineFactoryCoefficients.weight, div_div]
  · have he : n = 2 * (n / 2) + 1 := by omega
    rw [he, ArcsineFactoryCoefficients.coefficient_odd]
    have hi : (2 * (n / 2) + 1 + 1) / 2 = n / 2 + 1 := by omega
    have ho : (2 * (n / 2) + 1 + 1) % 2 = 0 := by omega
    simp [raw, index, factor, hi, ho, FactoryFractions.Fraction.value, Rat.mkRat_eq_div,
      ArcsineFactoryCoefficients.weight, div_div]

def coefficient {rT : Type} : Exp rT := pl%
  fun n,
    let degree := n + #1;
    let k := degree / #2;
    let factor := (if degree % #2 = #1 then degree else degree - #1);
    (&Occil.FactoryExtra.choose (#2 * k) k, &Occil.FactoryExtra.intPower #4 k * factor)

private def prepared {rT : Type} (k f : ℕ) : Exp rT := pl%
  (&Occil.FactoryExtra.choose (#2 * #int (k : ℤ)) #int (k : ℤ),
    &Occil.FactoryExtra.intPower #4 #int (k : ℤ) * #int (f : ℤ))

private instance choose_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance power_closed {rT : Type} : ClosedExp (Occil.FactoryExtra.intPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.intPower, Exp.fv]

/-- Closed binder form of the source callback. -/
def coefficientCode {rT : Type} : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let one : Exp rT := .lit (.int 1)
  let two : Exp rT := .lit (.int 2)
  let choose := .app (.app Occil.FactoryExtra.choose (.binop .mult two (.bvar 1))) (.bvar 1)
  let power := .app (.app Occil.FactoryExtra.intPower (.lit (.int 4))) (.bvar 1)
  let factor := .cond (.binop .eq (.binop .mod (.bvar 1) two) one) (.bvar 1)
    (.binop .minus (.bvar 1) one)
  .lam (bind (.binop .plus (.bvar 0) one)
    (bind (.binop .div (.bvar 0) two)
      (bind factor (.pair choose (.binop .mult power (.bvar 0))))))

theorem coefficient_eq_code {rT : Type} : (coefficient : Exp rT) = coefficientCode := by
  simp [coefficient, coefficientCode, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.closeRec]

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem parity_test (n : ℕ) :
    (((n : ℤ) + 1) % 2 == 1) = decide ((n + 1) % 2 = 1) := by
  by_cases h : (n + 1) % 2 = 1
  · have ht : (((n : ℤ) + 1) % 2 == 1) = true := beq_iff_eq.mpr (by omega)
    simp [h, ht]
  · have hf : (((n : ℤ) + 1) % 2 == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [h, hf]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_prepared (E : CoPset) (k f : ℕ) :
    ⊢ tglWp E (prepared k f)
      (fun v : Val rT => iprop(⌜v = Val.pair (.int k.centralBinom)
        (.int ((4 ^ k * f : ℕ) : ℤ))⌝)) := by
  twp_bind pl(&Occil.FactoryExtra.intPower #4 #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower E 4 k
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  rw [show (2 : ℤ) * k = ((2 * k : ℕ) : ℤ) by omega]
  twp_bind pl(&Occil.FactoryExtra.choose #int ((2 * k : ℕ) : ℤ) #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryChoose.twp_choose E (2 * k) k
  iintro %v %hv
  subst v
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  simp [Exp.ofVal, Nat.centralBinom]

/-- The source callback returns its unreduced central-binomial coefficient pair. -/
theorem twp_coefficient (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&coefficient #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)) := by
  iterate 4 twp_pure
  rw [show ((n : ℤ) + 1) / 2 = ((index n : ℕ) : ℤ) by unfold index; omega]
  iterate 3 twp_pure
  rw [int_beq, parity_test n]
  by_cases ho : (n + 1) % 2 = 1
  · rw [decide_eq_true ho]
    iterate 2 twp_pure
    have h := twp_prepared (rT := rT) (GF := GF) E (index n) (n + 1)
    simp [prepared, Nat.cast_add, Nat.cast_one] at h
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    isimp only [raw, factor, ho, ite_true, FactoryFractions.Fraction.encode,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    iapply h
  · rw [decide_eq_false ho]
    iterate 3 twp_pure
    rw [show (n : ℤ) + 1 - 1 = n by omega]
    have h := twp_prepared (rT := rT) (GF := GF) E (index n) n
    simp [prepared] at h
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    isimp only [raw, factor, ho, ite_false, FactoryFractions.Fraction.encode,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    iapply h

end specification

end SampLib.ArcsineCoefficients
