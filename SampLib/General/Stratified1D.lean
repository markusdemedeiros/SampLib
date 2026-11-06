import SampLib.General.Laws.Stratified1D
import SampLib.Core.Syntax.UniformRanges
import Samplers.General.Points

/-! # Independent jitter in consecutive integer strata

The boundaries are rounded down exactly as in the implementation. Each stratum
is nonempty when the number of strata lies between one and the grid scale.
-/

open ProbLang
open SampLib.RndIntExcRange (rndIntExcRange_openRec rndIntExcRange_closeRec)
open scoped ENNReal

namespace SampLib.Stratified1D

noncomputable section

private def build {rT : Type _} (scale strata : ℕ) : Exp rT := pl%
  rec draw index := if index = #int (strata : ℤ) then inl(#()) else
    let lower := index * #int (scale : ℤ) / #int (strata : ℤ);
    let upper := (index + #1) * #int (scale : ℤ) / #int (strata : ℤ);
    inr((&Occil.rndIntExcRange lower upper, draw (index + #1)))

private theorem boundary_cast (scale strata i : ℕ) :
    ((boundary scale strata i : ℕ) : ℤ) = (i : ℤ) * scale / strata := by
  simp [boundary, Int.natCast_ediv]

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : ℤ) (xs : List ℤ) :
    pl(inr(({Exp.ofVal (Val.int x)}, {Exp.ofVal (listVal Val.int xs)}))) =
      Exp.ofVal (listVal Val.int (x :: xs) : Val rT) := by
  simp [Exp.ofVal, listVal]

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem valid_test (scale strata : ℕ) (hs : 0 < strata) (h : strata ≤ scale) :
    Bool.or (decide ((strata : ℤ) ≤ 0)) (decide ((scale : ℤ) < strata)) = false := by
  have h' : (strata : ℤ) ≤ scale := by exact_mod_cast h
  simp [Nat.ne_of_gt hs, not_lt.mpr h']

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_build (E : CoPset) (scale strata : ℕ) (hs : 0 < strata)
    (h : strata ≤ scale) (n i : ℕ) (hi : i + n = strata) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂ListProduct.law (coordinate scale strata hs h) i n) -∗
      tglWp E pl(&(build (rT := rT) scale strata) #int (i : ℤ))
        (fun v : Val rT => iprop(∃ ys : List ℤ, ⌜v = listVal Val.int ys⌝ ∗ ↯ (F ys))) := by
  induction n generalizing i F with
  | zero =>
    have he : i = strata := by omega
    subst i
    iintro Hcredit
    twp_pures
    rw [int_beq, beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [ListProduct.law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    have hne : (i : ℤ) ≠ strata := by omega
    have hi' : (i + 1) + n = strata := by omega
    iintro Hcredit
    twp_pures
    rw [int_beq, beq_eq_false_iff_ne.mpr hne]
    iterate 9 twp_pure
    simp only [rndIntExcRange_openRec, rndIntExcRange_closeRec]
    rw [← Nat.cast_add_one]
    twp_bind pl(&(build (rT := rT) scale strata) #int ((i + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation scale strata hs h i n F] at Hcredit
      iapply (IH (i + 1) hi'
        (fun ys => ∫⁻ x, F (x :: ys) ∂coordinate scale strata hs h i)) $$ Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.rndIntExcRange
      #int ((i : ℤ) * scale / strata) #int (((i + 1 : ℕ) : ℤ) * scale / strata))
    rw [← boundary_cast, ← boundary_cast]
    isimp only [coordinate] at Hcredit
    iapply ((RndIntExcRange.rndIntExcRange_distSpec E (boundary scale strata i)
      (boundary scale strata (i + 1)) (Int.ofNat_lt.mpr (boundary_lt scale strata i hs h))).wp
      (fun x => F (x :: ys)) (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.int (x :: ys)))
    iexists x :: ys
    iframe Hcredit
    itrivial

theorem stratified1D_distSpec (E : CoPset) (scale strata : ℕ) (hs : 0 < strata)
    (h : strata ≤ scale) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.stratified1D #int (scale : ℤ) #int (strata : ℤ) #())
      (law scale strata hs h) (listVal Val.int) where
  spec F _ := by
    have hbuild := twp_build (rT := rT) (GF := GF) E scale strata hs h strata 0
      (Nat.zero_add strata) F
    simp [build, Exp.close, Exp.closeRec] at hbuild
    iintro Hcredit
    twp_pures
    rw [valid_test scale strata hs h]
    twp_pure
    twp_pure
    simp only [rndIntExcRange_openRec, rndIntExcRange_closeRec]
    isimp only [law] at Hcredit
    iapply hbuild
    iexact Hcredit

end specification

end

end SampLib.Stratified1D
