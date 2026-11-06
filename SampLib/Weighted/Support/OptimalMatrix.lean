import SampLib.Weighted.Support.OptimalEncode
import SampLib.Weighted.Support.OptimalParameters
import SampLib.Common.WeightedValidation
import SampLib.Weighted.Syntax.OptimalSource

/-! # Exact deterministic preprocessing of the original cyclic matrix -/

open ProbLang

namespace SampLib.Optimal

open OptimalEncoding OptimalMatrix

@[pl_fold] private def valuesCode {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (D : ℕ) : Exp rT :=
  .cond (.binop .eq (.lit (.int (D - ws.sum : ℕ))) (.lit (.int 0)))
    (listValNatInts ws).fst
    (.app (.lam (.app (.bvar 0) (listValNatInts ws).fst)) (Program.append (D - ws.sum)))

@[pl_fold] private def indexCode {rT : Type} [ProbLangℝ rT] (ws : List ℕ) (D : ℕ) : Exp rT := pl%
  if #int ((D - ws.sum : ℕ) : ℤ) = #0 then #(-1) else
    &Occil.length &(listValNatInts ws).fst

private theorem zero_test {rT : Type} [BEq rT] (a : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int 0) = decide (a = 0) := by
  change decide ((a : ℤ) = 0) = decide (a = 0)
  simp only [Int.natCast_eq_zero]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

section helpers

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ListValues.listVal_openRec
  WeightedValidation.validWeights_openRec WeightedValidation.validWeights_closeRec
  WeightedValidation.sumInts_openRec WeightedValidation.sumInts_closeRec

private theorem twp_values (E : CoPset) (ws : List ℕ) (D : ℕ) :
    ⊢ tglWp E (valuesCode ws D)
      (fun v : Val rT => iprop(⌜v = listValNatInts (values ws D)⌝)) := by
  unfold valuesCode
  twp_pure
  rw [zero_test]
  by_cases hr : D - ws.sum = 0
  · rw [decide_eq_true hr]
    twp_pure
    simp only [values, hr, ite_true]
    change ⊢ tglWp E (Exp.ofVal (listValNatInts (rT := rT) ws)) _
    iapply tglWp_value
    ipureintro
    rfl
  · rw [decide_eq_false hr]
    iterate 2 twp_pure
    simp only [values, hr, ite_false]
    iapply twp_append (rT := rT) (GF := GF) E (D - ws.sum) ws

private theorem twp_index (E : CoPset) (ws : List ℕ) (D : ℕ) :
    ⊢ tglWp E (indexCode ws D)
      (fun v : Val rT => iprop(⌜v = Val.int (rejectionIndex ws D)⌝)) := by
  unfold indexCode
  twp_pure
  rw [zero_test]
  by_cases hr : D - ws.sum = 0
  · rw [decide_eq_true hr]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp only [rejectionIndex, hr, ite_true]
  · rw [decide_eq_false hr]
    twp_pure
    simp only [rejectionIndex, hr, ite_false]
    iapply twp_length (rT := rT) (GF := GF) E (fun n : ℕ => Val.int (n : ℤ)) ws

end helpers

attribute [local pl_step_simp] ListValues.listVal_openRec
  WeightedValidation.validWeights_openRec WeightedValidation.validWeights_closeRec
  WeightedValidation.sumInts_openRec WeightedValidation.sumInts_closeRec
  WeightedIntegerPower.integerPower_openRec WeightedIntegerPower.integerPower_closeRec
  Program.bitLength_openRec Program.length_openRec

/-- Every valid nonnegative weight vector produces exactly the repaired cyclic table. -/
theorem twp_optimalMatrix (E : CoPset) (ws : List ℕ) (hs : 0 < ws.sum) :
    ⊢ tglWp E pl(&Occil.WeightedVariants.optimalMatrix &(listValNatInts ws).fst)
      (fun v : Val rT => iprop(⌜v = Table.value (create ws)⌝)) := by
  let k := ws.sum.size
  let p := OptimalParameters.selected ws.sum
  have hp : OptimalParameters.Valid k ws.sum p := OptimalParameters.selected_valid hs
  have hD : ws.sum ≤ denominator k p.1 := by simpa only [hp.2.1] using hp.2.2
  have hmake : create ws =
      ⟨(values ws p.2).map (binary k p.1), k, p.1, rejectionIndex ws p.2⟩ := rfl
  rw [hmake, Program.matrix_code_eq (rT := rT)]
  twp_pure
  twp_bind pl(&Occil.Weighted.validWeights &(listValNatInts ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights (rT := rT) (GF := GF) E ws hs
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listValNatInts ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts (rT := rT) (GF := GF) E ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.WeightedVariants.bitLength #int (ws.sum : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply BitLength.twp_bitLength (rT := rT) (GF := GF) E ws.sum
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.Weighted.integerPower #2 #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply WeightedIntegerPower.twp_integerPower (rT := rT) (GF := GF) E 2 k
  iintro %v %hv
  subst v
  rw [show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by norm_cast]
  iterate 2 twp_pure
  twp_bind pl(&(Program.parameters k ws.sum : Exp rT) #0 #int (k : ℤ)
    #int ((2 ^ k : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_parameters (rT := rT) (GF := GF) E k ws.sum 0 k (2 ^ k)
  iintro %v %hv
  change v = parameterValue p at hv
  subst v
  simp only [parameterValue]
  rw [hp.2.1]
  iterate 5 twp_pure
  twp_pure
  rw [← Nat.cast_sub hD]
  twp_pure
  twp_bind (valuesCode ws (denominator k p.1) : Exp rT)
  iapply tglWp_wand
  isplitl []
  · iapply twp_values (rT := rT) (GF := GF) E ws (denominator k p.1)
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  twp_bind (indexCode ws (denominator k p.1) : Exp rT)
  iapply tglWp_wand
  isplitl []
  · iapply twp_index (rT := rT) (GF := GF) E ws (denominator k p.1)
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&(Program.encode k p.1 (denominator k p.1) : Exp rT)
    &(listValNatInts (values ws (denominator k p.1))).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_encode (rT := rT) (GF := GF) E k p.1 hp.1 (values ws (denominator k p.1))
  iintro %v %hv
  subst v
  change ⊢ tglWp E (Exp.ofVal (Table.value (rT := rT)
    ⟨(values ws (denominator k p.1)).map (binary k p.1), k, p.1,
      rejectionIndex ws (denominator k p.1)⟩)) _
  iapply tglWp_value
  ipureintro
  rfl

end specification

end SampLib.Optimal
