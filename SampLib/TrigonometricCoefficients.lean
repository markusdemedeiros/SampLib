import SampLib.FactorialCallback
import SampLib.FactoryIntegerPower
import SampLib.FactoryFractions

/-! # Exact coefficient callbacks used by the sinc and cosine factories -/

open ProbLang

namespace SampLib.TrigonometricCoefficients

open FactorialCallback

def cosine {rT : Type} : Exp rT := pl%
  fun n, (#1, &factorial (#2 * n))

def sinc {rT : Type} (a b : ℤ) : Exp rT := pl%
  fun n, (&Occil.FactoryExtra.intPower #int a n,
    &Occil.FactoryExtra.intPower #int b n * &factorial (#2 * n + #1))

/-- The callback values after evaluation of the source's local factorial. -/
def cosineCode {rT : Type} : Exp rT :=
  .lam (.pair (.lit (.int 1))
    (.app FactorialCallback.factorialCode (.binop .mult (.lit (.int 2)) (.bvar 0))))

def sincCode {rT : Type} (a b : ℤ) : Exp rT :=
  let power z := .app (.app Occil.FactoryExtra.intPower (.lit (.int z))) (.bvar 0)
  .lam (.pair (power a) (.binop .mult (power b)
    (.app FactorialCallback.factorialCode
      (.binop .plus (.binop .mult (.lit (.int 2)) (.bvar 0)) (.lit (.int 1))))))

def cosineFraction (n : ℕ) : FactoryFractions.Fraction :=
  ⟨1, (2 * n).factorial, Nat.factorial_pos _⟩

def sincFraction (a : ℤ) (b : ℕ) (hb : 0 < b) (n : ℕ) : FactoryFractions.Fraction :=
  ⟨a ^ n, b ^ n * (2 * n + 1).factorial,
    Nat.mul_pos (Nat.pow_pos hb) (Nat.factorial_pos _)⟩

theorem cosineFraction_value (n : ℕ) :
    (cosineFraction n).value = (1 : ℚ) / (2 * n).factorial := by
  simp [cosineFraction, FactoryFractions.Fraction.value, Rat.mkRat_eq_div]

theorem sincFraction_value (a : ℤ) (b : ℕ) (hb : 0 < b) (n : ℕ) :
    (sincFraction a b hb n).value = ((a : ℚ) / b) ^ n / (2 * n + 1).factorial := by
  simp only [sincFraction, FactoryFractions.Fraction.value, Rat.mkRat_eq_div,
    Int.cast_pow, Nat.cast_mul, Nat.cast_pow, div_pow, div_div]

private theorem power_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.intPower = Occil.FactoryExtra.intPower :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem power_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.intPower : Exp rT) = Occil.FactoryExtra.intPower :=
  Exp.closeRec_fresh x _ k (by simp [Occil.FactoryExtra.intPower, Exp.fv])

theorem cosine_eq_code {rT : Type} : (cosine : Exp rT) = cosineCode := by
  simp [cosine, cosineCode, FactorialCallback.factorial_eq_code, Exp.close, Exp.closeRec,
    FactorialCallback.factorialCode]

theorem sinc_eq_code {rT : Type} (a b : ℤ) : (sinc a b : Exp rT) = sincCode a b := by
  simp [sinc, sincCode, FactorialCallback.factorial_eq_code, Exp.close, Exp.closeRec,
    FactorialCallback.factorialCode, power_close]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_cosine (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&cosine #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.pair (.int 1) (.int (2 * n).factorial)⌝)) := by
  iterate 2 twp_pure
  rw [show (2 : ℤ) * n = ((2 * n : ℕ) : ℤ) by omega]
  twp_bind pl(&factorial #int ((2 * n : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_factorial E (2 * n)
  iintro %v %hv
  subst v
  twp_value
  imodintro
  ipureintro
  rfl

theorem twp_sinc (E : CoPset) (a b : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&(sinc a b) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.pair (.int (a ^ n))
        (.int (b ^ n * (2 * n + 1).factorial))⌝)) := by
  twp_pure
  simp only [power_open, power_close, factorial_openRec, factorial_closeRec]
  iterate 2 twp_pure
  rw [show (2 : ℤ) * n + 1 = ((2 * n + 1 : ℕ) : ℤ) by omega]
  twp_bind pl(&factorial #int ((2 * n + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_factorial E (2 * n + 1)
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.FactoryExtra.intPower #int b #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower E b n
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.FactoryExtra.intPower #int a #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply FactoryIntegerPower.twp_intPower E a n
  iintro %v %hv
  subst v
  twp_value
  imodintro
  ipureintro
  rfl

theorem twp_cosineFraction (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&cosine #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (cosineFraction n).encode⌝)) := by
  simpa only [cosineFraction, FactoryFractions.Fraction.encode] using twp_cosine E n

theorem twp_sincFraction (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) (n : ℕ) :
    ⊢ tglWp E pl(&(sinc a (b : ℤ)) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (sincFraction a b hb n).encode⌝)) := by
  simpa only [sincFraction, FactoryFractions.Fraction.encode, Nat.cast_mul, Nat.cast_pow]
    using twp_sinc E a (b : ℤ) n

end specification

end SampLib.TrigonometricCoefficients
