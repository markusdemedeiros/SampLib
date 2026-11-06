import SampLib.Constants.Laws.EulerMascheroniSeries
import SampLib.Common.Laws.BinaryRounding
import SampLib.Constants.FromPositiveSeries
import SampLib.Constants.Support.PositiveSeriesClosed
import Samplers.Constants.Special

/-! # Euler's constant from Sondow's positive binary-length series -/

open ProbLang

namespace SampLib.EulerMascheroni

noncomputable section

open EulerMascheroniSeries

@[pl_fold] private def bits {rT : Type} : Exp rT := pl%
  rec count n := if n = #0 then #0 else #1 + count (n / #2)

private instance bits_closed {rT : Type} : ClosedExp (bits : Exp rT) where
  lc := by is_lc
  fv := by simp [bits, Exp.fv]

@[pl_fold] private def getterCode {rT : Type} : Exp rT := pl%
  fun n,
    if n = #0 then (#1, (#2, (#1, #2))) else
      let b := &bits n;
      (b, (#2 * n * (#2 * n + #1) * (#2 * n + #2),
        ((#2 + b) * n + #1, #16 * n * n * n)))

private def getter {rT : Type} : Val rT :=
  ⟨getterCode, by unfold getterCode; exact .lam (by is_lc), by is_lc⟩

/-- Binding the source bit counter gives exactly the verified series callback. -/
private theorem source_transport {rT : Type} :
    pl(&Occil.Constants.fromPositiveSeries &(getter : Val rT).fst #()) =
      (pl% &Occil.Constants.fromPositiveSeries (fun n,
        if n = #0 then (#1, (#2, (#1, #2))) else
          let b := (rec count n := if n = #0 then #0 else #1 + count (n / #2)) n;
          (b, (#2 * n * (#2 * n + #1) * (#2 * n + #2),
            ((#2 + b) * n + #1, #16 * n * n * n)))) #() : Exp rT) := by
  kernel_rfl

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem nonzero_test (n : ℕ) (hn : 0 < n) : ((n : ℤ) == 0) = false := by
  simp
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bits (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(bits : Exp rT) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (n.size : ℤ)⌝)) := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
    by_cases hn : n = 0
    · subst n
      twp_pures
      twp_value
      imodintro
      itrivial
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      twp_pures
      rw [int_beq, nonzero_test n hn']
      iterate 2 twp_pure
      have hrec := IH (n / 2) (Nat.div_lt_self hn' (by decide))
      rw [Int.natCast_div] at hrec
      twp_bind pl(&(bits : Exp rT) #int ((n : ℤ) / 2))
      iapply tglWp_wand
      isplitl []
      · iapply hrec
      iintro %v %hv
      subst v
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply congrArg Val.int
      simp [BinaryRounding.size_step hn']

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_getter (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(getter : Val rT).fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = FromPositiveSeries.encodeCoefficient
        (parameters.coefficient n)⌝)) := by
  by_cases hn : n = 0
  · subst n
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [FromPositiveSeries.encodeCoefficient, parameters, coefficient]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    iterate 2 twp_pure
    rw [int_beq, nonzero_test n hn']
    twp_pure
    twp_bind pl(&(bits : Exp rT) #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_bits E n
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [FromPositiveSeries.encodeCoefficient, parameters, coefficient, hn,
      Nat.cast_add, Nat.cast_mul, Exp.ofVal]

/-- The original bit-count getter and its certified remainder sample Euler's constant. -/
theorem eulerMascheroni_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.eulerMascheroni #())
      (RealCoin.law (FromPositiveSeries.bias parameters)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    have h := (FromPositiveSeries.fromPositiveSeries_distSpec
      (rT := rT) (GF := GF) E parameters getter (twp_getter E)).spec F hF
    simp [source_transport, Exp.close, Exp.closeRec] at h
    iapply h $$ Hcredit

end specification

end

end SampLib.EulerMascheroni
