import SampLib.Templates
import Samplers.Bernoulli.Arithmetic

/-! # Deterministic integer powers in coin factories -/

open ProbLang

namespace SampLib.FactoryIntegerPower

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The checked object-language recursion computes the usual integer power. -/
theorem twp_intPower (E : CoPset) (base : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.FactoryExtra.intPower #int base #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (base ^ n)⌝)) := by
  induction n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp
  | succ n IH =>
    iterate 8 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.FactoryExtra.intPower #int base #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [pow_succ, mul_comm]

end specification

end SampLib.FactoryIntegerPower
