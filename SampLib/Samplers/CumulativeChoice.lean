import SampLib.Distributions.CategoricalCDF
import SampLib.WeightedValidation
import SampLib.Syntax.ClosedExp

/-! # Categorical sampling by cumulative preprocessing and bisection

The prefix scan constructs the canonical categorical CDF. The verified table
draw then returns precisely that categorical law on integer labels.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.CumulativeChoice

noncomputable section

private theorem listVal_map_cast {rT : Type _} [ProbLangℝ rT] (xs : List ℕ) :
    listVal (fun z : ℤ => Val.int z) (xs.map (fun n : ℕ => (n : ℤ))) =
      (listVal (fun n : ℕ => Val.int n) xs : Val rT) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, listVal, ih]

private theorem table_encoding {rT : Type _} [ProbLangℝ rT] (ws : List ℕ)
    (hs : 0 < ws.sum) :
    CumulativeDraw.table (rT := rT) (CategoricalCDF.model ws hs) ws.length =
      Val.pair (.int (ws.sum : ℤ))
        (listVal (fun n : ℕ => Val.int n) (CategoricalCDF.scan ws 0)) := by
  unfold CumulativeDraw.table
  rw [← CategoricalCDF.scan_eq_cumulative, listVal_map_cast]
  rfl

private def scan {rT : Type _} : Exp rT := pl%
  rec build xs running := case! xs
    | inl(u) => inl(#())
    | inr(p) =>
      let next := running + fst(p);
      inr((next, build (snd(p)) next))

private instance cumulativeDraw_closed {rT : Type _} :
    ClosedExp (Occil.Weighted.cumulativeDraw : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.Weighted.cumulativeDraw, Occil.uniformInt, Occil.getAt,
      Occil.length, Exp.fv]

private instance cumulativeTable_closed {rT : Type _} :
    ClosedExp (Occil.Weighted.cumulativeTable : Exp rT) where
  lc := by is_lc
  fv := by
    simp [Occil.Weighted.cumulativeTable, WeightedValidation.validWeights_fv,
      WeightedValidation.sumInts_fv, Exp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_scan (E : CoPset) (ws : List ℕ) (running : ℕ) :
    ⊢ tglWp E pl(&scan &(listVal (fun n : ℕ => Val.int n) ws).fst #int (running : ℤ))
      (fun v => iprop(⌜v = listVal (fun n : ℕ => Val.int n)
        (CategoricalCDF.scan ws running)⌝)) := by
  induction ws generalizing running with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons w ws ih =>
    simp only [listVal]
    iterate 9 twp_pure
    rw [← Nat.cast_add]
    twp_bind pl(&scan &(listVal (fun n : ℕ => Val.int n) ws).fst
      #int ((running + w : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply ih (running + w)
    iintro %v %hv
    subst v
    simp only [Exp.ofVal]
    let result : Val rT := .inr (.pair (.int ((running + w : ℕ) : ℤ))
      (listVal (fun n : ℕ => Val.int n) (CategoricalCDF.scan ws (running + w))))
    iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
    ipureintro
    rw [CategoricalCDF.scan_cons]
    exact Val.ext rfl

private theorem twp_cumulativeTable (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum) :
    ⊢ tglWp E pl(&Occil.Weighted.cumulativeTable
      &(listVal (fun n : ℕ => Val.int n) ws).fst)
      (fun v => iprop(⌜v = CumulativeDraw.table (CategoricalCDF.model ws hs) ws.length⌝)) := by
  twp_pure
  simp only [WeightedValidation.validWeights_openRec, WeightedValidation.validWeights_closeRec]
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws hs
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [WeightedValidation.sumInts_openRec, WeightedValidation.sumInts_closeRec]
  twp_bind pl(&scan &(listVal (fun n : ℕ => Val.int n) ws).fst #0)
  iapply tglWp_wand
  isplitl []
  · iapply twp_scan E ws 0
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  iapply (tglWp_value_of_toVal (Val.toVal?_fst (Val.pair (.int (ws.sum : ℤ))
    (listVal (rT := rT) (fun n : ℕ => Val.int n) (CategoricalCDF.scan ws 0)))))
  ipureintro
  rw [table_encoding]

variable [ProbLangDist.IsUniformInt rT]

/-- Prefix preprocessing and bisection realize the canonical categorical law. -/
theorem cumulativeChoice_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.cumulativeChoice
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (CategoricalCDF.law ws) Val.int := by
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.Weighted.cumulativeTable &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_cumulativeTable E ws (NeZero.pos ws.sum)
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  isimp only [← CategoricalCDF.law_eq ws (NeZero.pos ws.sum)] at Hcredit
  iapply ((CumulativeDraw.cumulativeDraw_distSpec E (CategoricalCDF.model ws
    (NeZero.pos ws.sum)) ws.length rfl rfl).wp F hF _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit
  itrivial

end specification

end

end SampLib.CumulativeChoice
