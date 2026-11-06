import SampLib.Core.DistributionMap
import SampLib.Core.SamplerStep
import SampLib.Core.ListOperations
import SampLib.General.Syntax.Stratified
import SampLib.General.Laws.StratifiedBox

/-! # Cartesian stratification with independent repeated jitter

Every cell receives the requested number of independent points. The product of
the cell laws is flattened in cell order, exactly as in the implementation.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.StratifiedBox

noncomputable section

private def sampler {rT : Type _} [ProbLangℝ rT] (scale bins dimension cell : ℕ) : Val rT :=
  ⟨pl(fun u, &Occil.General.stratifiedCell #int (scale : ℤ) #int (bins : ℤ)
    #int (dimension : ℤ) #int (cell : ℤ)), .lam (by is_lc), by is_lc⟩

private def build {rT : Type _} [ProbLangℝ rT]
    (scale bins dimension perCell : ℕ) : Exp rT := pl%
  rec draw cell := if cell = #int ((bins ^ dimension : ℕ) : ℤ) then inl(#()) else
    &Occil.General.append
      (&Occil.repeatSample (fun u, &Occil.General.stratifiedCell
        #int (scale : ℤ) #int (bins : ℤ) #int (dimension : ℤ) cell)
        #int (perCell : ℤ))
      (draw (cell + #1))

private def loopValue {rT : Type _} [ProbLangℝ rT]
    (scale bins dimension perCell : ℕ) : Val rT :=
  ⟨build scale bins dimension perCell, .fix (by is_lc), by is_lc⟩

private theorem loopValue_fst {rT : Type _} [ProbLangℝ rT]
    (scale bins dimension perCell : ℕ) :
    (loopValue (rT := rT) scale bins dimension perCell).fst =
      build scale bins dimension perCell := rfl

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem valid_test (scale bins dimension : ℕ) (hb : 0 < bins)
    (h : bins ≤ scale) (hd : 0 < dimension) :
    Bool.or (Bool.or (decide ((bins : ℤ) ≤ 0))
      (decide ((scale : ℤ) < bins))) (decide ((dimension : ℤ) ≤ 0)) = false := by
  simp [Nat.ne_of_gt hb, Nat.ne_of_gt hd, not_lt.mpr (Int.ofNat_le.mpr h)]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem sampler_spec (E : CoPset) (scale bins dimension cell : ℕ)
    (hb : 0 < bins) (h : bins ≤ scale) (hd : 0 < dimension) (hc : cell < bins ^ dimension) :
    IsDistSpec (GF := GF) E pl(&(sampler (rT := rT) scale bins dimension cell).fst #())
      (StratifiedCell.law scale bins hb h dimension cell) (listVal Val.int) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [StratifiedCell.stratifiedCell_openRec, StratifiedCell.stratifiedCell_closeRec]
    iapply (StratifiedCell.stratifiedCell_distSpec E scale bins dimension cell hb h hd hc).spec
      F hF $$ Hcredit

private theorem chunk_spec (E : CoPset) (scale bins dimension perCell cell : ℕ)
    (hb : 0 < bins) (h : bins ≤ scale) (hd : 0 < dimension) (hc : cell < bins ^ dimension) :
    IsDistSpec (GF := GF) E
      pl(&Occil.repeatSample &(sampler (rT := rT) scale bins dimension cell).fst
        #int (perCell : ℤ))
      (chunkLaw scale bins hb h dimension perCell cell) (listVal (listVal Val.int)) := by
  have hs := SampleWithReplacement.repeatSample_distSpec (rT := rT) (GF := GF) E
    (StratifiedCell.law scale bins hb h dimension cell) (listVal Val.int)
    (sampler scale bins dimension cell) (sampler_spec E scale bins dimension cell hb h hd hc)
    perCell
  exact hs.map (fun ys => List.ofFn ys) (measurable_of_countable _)
    (listVal (listVal Val.int)) (fun _ => rfl)

private theorem twp_build (E : CoPset) (scale bins dimension perCell : ℕ)
    (hb : 0 < bins) (h : bins ≤ scale) (hd : 0 < dimension)
    (n cell : ℕ) (hi : cell + n = bins ^ dimension) (F : List (List ℤ) → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂lawFrom scale bins hb h dimension perCell cell n) -∗
      tglWp E pl(&(build (rT := rT) scale bins dimension perCell) #int (cell : ℤ))
        (fun v : Val rT => iprop(∃ ys : List (List ℤ),
          ⌜v = listVal (listVal Val.int) ys⌝ ∗ ↯ (F ys))) := by
  induction n generalizing cell F with
  | zero =>
    have he : cell = bins ^ dimension := by omega
    subst cell
    iintro Hcredit
    twp_pures
    rw [int_beq, beq_self_eq_true]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [expectation_zero] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    have hc : cell < bins ^ dimension := by omega
    have hnPow : (cell : ℤ) ≠ (bins : ℤ) ^ dimension := by exact_mod_cast hc.ne
    have hi' : (cell + 1) + n = bins ^ dimension := by omega
    iintro Hcredit
    rw [← loopValue_fst]
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    twp_pure
    twp_pure
    rw [int_beq, beq_eq_false_iff_ne.mpr hnPow]
    twp_pure
    twp_pure
    simp only [ListOperations.append_openRec, ListOperations.repeatSample_openRec,
      StratifiedCell.stratifiedCell_openRec]
    rw [← Nat.cast_add_one]
    twp_bind pl(&(loopValue (rT := rT) scale bins dimension perCell).fst
      #int ((cell + 1 : ℕ) : ℤ))
    rw [loopValue_fst]
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation scale bins hb h dimension perCell cell n F] at Hcredit
      iapply (IH (cell + 1) hi'
        (fun ys => ∫⁻ chunk, F (chunk ++ ys) ∂chunkLaw scale bins hb h dimension perCell cell))
        $$ Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.repeatSample &(sampler (rT := rT) scale bins dimension cell).fst
      #int (perCell : ℤ))
    iapply ((chunk_spec E scale bins dimension perCell cell hb h hd hc).wp
      (fun chunk => F (chunk ++ ys)) (measurable_of_countable _) _) $$ Hcredit
    iintro %chunk Hcredit
    twp_bind pl(&Occil.General.append &(listVal (listVal Val.int) chunk).fst
      &(listVal (listVal Val.int) ys).fst)
    iapply tglWp_wand
    isplitl []
    · iapply ListOperations.twp_append E (listVal Val.int) chunk ys
    iintro %v %hv
    iapply (tglWp_value (v := v))
    iexists chunk ++ ys
    iframe Hcredit
    ipureintro
    exact hv

theorem stratifiedBox_distSpec (E : CoPset) (scale bins dimension perCell : ℕ)
    (hb : 0 < bins) (h : bins ≤ scale) (hd : 0 < dimension) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.stratifiedBox #int (scale : ℤ) #int (bins : ℤ)
        #int (dimension : ℤ) #int (perCell : ℤ) #())
      (law scale bins hb h dimension perCell) (listVal (listVal Val.int)) where
  spec F _ := by
    have hbuild := twp_build (rT := rT) (GF := GF) E scale bins dimension perCell hb h hd
      (bins ^ dimension) 0 (Nat.zero_add _) F
    simp [build, Exp.close, Exp.closeRec] at hbuild
    iintro Hcredit
    twp_pures
    simp only [Bool.or_false]
    rw [valid_test scale bins dimension hb h hd]
    twp_pure
    simp only [GeneralIntegerPower.integerPower_closeRec,
      GeneralIntegerPower.integerPower_openRec]
    twp_bind pl(&Occil.General.integerPower #int (bins : ℤ) #int (dimension : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply GeneralIntegerPower.twp_integerPower E (bins : ℤ) dimension
    iintro %v %hv
    subst v
    twp_pure
    twp_pure
    simp only [ListOperations.append_openRec, ListOperations.append_closeRec,
      ListOperations.repeatSample_openRec, ListOperations.repeatSample_closeRec,
      StratifiedCell.stratifiedCell_openRec, StratifiedCell.stratifiedCell_closeRec]
    isimp only [law] at Hcredit
    iapply hbuild
    iexact Hcredit

end specification

end

end SampLib.StratifiedBox
