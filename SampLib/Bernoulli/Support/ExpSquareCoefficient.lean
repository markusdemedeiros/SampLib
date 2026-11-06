import SampLib.Bernoulli.Laws.ExpSquareComplement
import SampLib.Bernoulli.Support.FactorialCallback
import SampLib.Bernoulli.Support.FactoryFractions

/-! # The literal factorial-pair coefficient callback -/

open ProbLang

namespace SampLib.ExpSquareCoefficient

noncomputable section

def coefficient (n : ℕ) : FactoryFractions.Fraction :=
  ⟨1, (n / 2).factorial, Nat.factorial_pos _⟩

theorem coefficient_value (n : ℕ) :
    ((coefficient n).value : ℝ) = AlternatingSeries.value ExpSquareComplement.parameters n := by
  rw [FactoryFractions.Fraction.cast_value]
  simp [coefficient, AlternatingSeries.value, ExpSquareComplement.parameters]

theorem coefficient_eq (n : ℕ) :
    (coefficient n).value = ExpSquareComplement.parameters.coefficient n := by
  have h := coefficient_value n
  change ((coefficient n).value : ℝ) = (ExpSquareComplement.parameters.coefficient n : ℝ) at h
  exact_mod_cast h

def callback {rT : Type} : Val rT :=
  ⟨.lam pl((#1, &FactorialCallback.factorial ({Exp.bvar 0} / #2))),
    .lam (by is_lc), by is_lc⟩

private theorem division (n : ℕ) : (n : ℤ) / 2 = (n / 2 : ℕ) :=
  (Int.natCast_ediv n 2).symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The deterministic callback returns the unreduced pair `(1, floor(n/2)!)`. -/
theorem twp_callback (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(callback : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (coefficient n).encode⌝)) := by
  twp_pure
  twp_bind pl(&FactorialCallback.factorial (#int (n : ℤ) / #2))
  twp_pure
  rw [division]
  iapply tglWp_wand
  isplitl []
  · iapply FactorialCallback.twp_factorial E (n / 2)
  iintro %v %hv
  subst v
  twp_value
  imodintro
  ipureintro
  rfl

end specification

end

end SampLib.ExpSquareCoefficient
