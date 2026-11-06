import SampLib.Bernoulli.Laws.ExpIntegral
import SampLib.Bernoulli.Support.FactorialCallback
import SampLib.Bernoulli.Support.FactoryFractions

/-! # The factorial-integral coefficient callback -/

open ProbLang

namespace SampLib.ExpIntegralCoefficient

noncomputable section

def coefficient (n : ℕ) : FactoryFractions.Fraction :=
  ⟨1, (n + 1).factorial, Nat.factorial_pos _⟩

theorem coefficient_value (n : ℕ) :
    (coefficient n).value = ExpIntegral.parameters.coefficient n := by
  have h : ((coefficient n).value : ℝ) = (ExpIntegral.parameters.coefficient n : ℝ) := by
    rw [FactoryFractions.Fraction.cast_value]
    simp [coefficient, ExpIntegral.parameters]
  exact_mod_cast h

def callback {rT : Type} : Val rT :=
  ⟨pl(fun n, let factorial := &FactorialCallback.factorial; (#1, factorial (n + #1))),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Execute the source's lexical factorial and its integer successor argument. -/
theorem twp_callback (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(callback : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (coefficient n).encode⌝)) := by
  iterate 2 twp_pure
  twp_bind pl(&FactorialCallback.factorial (#int (n : ℤ) + #1))
  twp_pure
  rw [← Nat.cast_add_one]
  iapply tglWp_wand
  isplitl []
  · iapply FactorialCallback.twp_factorial E (n + 1)
  iintro %v %hv
  subst v
  twp_value
  imodintro
  ipureintro
  rfl

end specification

end

end SampLib.ExpIntegralCoefficient
