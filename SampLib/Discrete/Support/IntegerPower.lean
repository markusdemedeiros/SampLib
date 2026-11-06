import SampLib.Templates
import Samplers.Discrete.Combinatorics
import Metrology.Iris.LocalBI

/-! # Deterministic integer powers used by discrete samplers -/

open ProbLang

namespace SampLib

private def powerLoop {rT : Type _} (base : ℤ) : Exp rT := pl%
  rec go n product := if n = #0 then product else go (n - #1) (product * #int base)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem power_step (base acc : ℤ) (n : ℕ) :
    (acc * base) * base ^ n = acc * base ^ (n + 1) := by ring

private theorem twp_powerLoop (E : CoPset) (base acc : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&(powerLoop base) #int (n : ℤ) #int acc)
      (fun v : Val rT => iprop(⌜v = Val.int (acc * base ^ n)⌝)) := by
  induction n generalizing acc with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp
  | succ n ih =>
    iterate 7 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    have h := ih (acc * base)
    rw [power_step] at h
    simp [powerLoop, Exp.close, Exp.closeRec] at h
    isimp [powerLoop, Exp.close, Exp.closeRec, Exp.ofVal]
    iapply h

/-- The accumulator loop computes the ordinary integer power. -/
theorem twp_integerPower (E : CoPset) (base : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.DiscreteExtra.integerPower #int base #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (base ^ n)⌝)) := by
  iterate 5 twp_pure
  have h := twp_powerLoop (rT := rT) (GF := GF) E base 1 n
  simp [powerLoop, Exp.close, Exp.closeRec] at h
  iapply h

end specification

end SampLib
