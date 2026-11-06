import SampLib.Templates
import Samplers.General.Points

/-! # Integer powers by an accumulating loop -/

open ProbLang

namespace SampLib.GeneralIntegerPower

private def power {rT : Type _} (base : ℤ) : Exp rT := pl%
  rec loop n acc := if n = #0 then acc else loop (n - #1) (acc * #int base)

private theorem step (base acc : ℤ) (n : ℕ) :
    (acc * base) * base ^ n = acc * base ^ (n + 1) := by rw [pow_succ']; ring

theorem integerPower_lc {rT : Type _} :
    (Occil.General.integerPower : Exp rT).IsLocallyClosed := by is_lc

theorem integerPower_fv {rT : Type _} :
    (Occil.General.integerPower : Exp rT).fv = ∅ := by
  simp [Occil.General.integerPower, Exp.fv]

@[simp] theorem integerPower_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.integerPower = Occil.General.integerPower :=
  (Exp.open_lc k e _ integerPower_lc).symm

@[simp] theorem integerPower_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.General.integerPower : Exp rT) = Occil.General.integerPower :=
  Exp.closeRec_fresh x _ k (by simp [integerPower_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_power (E : CoPset) (base : ℤ) (n : ℕ) (acc : ℤ) :
    ⊢ tglWp E pl(&(power (rT := rT) base) #int (n : ℤ) #int acc)
      (fun v : Val rT => iprop(⌜v = Val.int (acc * base ^ n)⌝)) := by
  induction n generalizing acc with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp
  | succ n IH =>
    have hrec := IH (acc * base)
    simp [power, Exp.close, Exp.closeRec] at hrec
    iterate 7 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right, ← step]
    isimp only [Exp.ofVal]
    iapply hrec

theorem twp_integerPower (E : CoPset) (base : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.General.integerPower #int base #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (base ^ n)⌝)) := by
  have h := twp_power (rT := rT) (GF := GF) E base n 1
  simp [power, Exp.close, Exp.closeRec] at h
  iterate 5 twp_pure
  iapply h

end specification

end SampLib.GeneralIntegerPower
