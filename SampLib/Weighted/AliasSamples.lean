import SampLib.Weighted.Syntax.AliasSamples
import SampLib.Core.BetaStep
import SampLib.Weighted.Support.WalkerSetup
import SampLib.Weighted.Support.WalkerBalance
import SampLib.Weighted.Support.WalkerDraw
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.Arrays
import SampLib.Core.ListOperations
import Samplers.Weighted.Sequential

/-! # Walker preprocessing followed by independent categorical draws -/

open ProbLang
open scoped ENNReal

namespace SampLib.AliasSamples

noncomputable section

abbrev natVal {rT : Type} [ProbLangℝ rT] (n : ℕ) : Val rT := Val.int n

/-- The ordered independent categorical vector. -/
abbrev law (ws : List ℕ) (count : ℕ) :=
  SampleWithReplacement.law (WeightedChoice.law ws) count

private def valid {rT : Type} : Exp rT := pl%
  rec check xs := case! xs | inl(u) => #true | inr(p) =>
    if fst(p) < #0 then #false else check (snd(p))

private theorem length_pos (ws : List ℕ) (h : 0 < ws.sum) : 0 < ws.length := by
  cases ws with
  | nil => simp at h
  | cons w ws => simp

private theorem positive_test (n : ℕ) (h : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := decide_eq_false (by omega)

private theorem weights_sum (ws : List ℕ) : (∑ i : Fin ws.length, ws.get i) = ws.sum := by
  simpa only [List.sum_ofFn] using congrArg List.sum (List.ofFn_get ws)

private theorem initial_work {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    ws.map (fun w => (natVal (ws.length * w) : Val rT)) =
      List.ofFn (WalkerBalance.natVal ∘
        (WalkerAlias.State.initial ws.get ws.sum).work) := by
  simpa only [List.map_ofFn, WalkerAlias.State.initial, Function.comp_def] using
    (congrArg (List.map (fun w => (natVal (ws.length * w) : Val rT))) (List.ofFn_get ws)).symm

private theorem initial_probability {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    List.replicate ws.length (natVal ws.sum : Val rT) =
      List.ofFn (WalkerBalance.natVal ∘
        (WalkerAlias.State.initial ws.get ws.sum).table.threshold) := by
  simp only [WalkerAlias.State.initial, Function.comp_def, List.ofFn_const]

private theorem initial_aliases {rT : Type} [ProbLangℝ rT] (ws : List ℕ) :
    (List.range' 0 ws.length).map (natVal (rT := rT)) =
      List.ofFn (WalkerBalance.indexVal ∘
        (WalkerAlias.State.initial ws.get ws.sum).table.target) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [WalkerAlias.State.initial, WalkerBalance.indexVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ArraySyntax.length_openRec ArraySyntax.length_closeRec
  WeightedValidation.sumInts_openRec WeightedValidation.sumInts_closeRec
  UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec
  ListOperations.repeatSample_openRec ListOperations.repeatSample_closeRec

private theorem source_beta (E : CoPset) (weights : Val rT) (count : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(weightedSource weights).fst #int count) Φ ⊢
      tglWp E pl(&(source (rT := rT)).fst &weights.fst #int count) Φ :=
  twp_beta E [.appL (.int count)] (.lam countBody) weights (source (rT := rT)).lc Φ

private theorem weighted_beta (E : CoPset) (weights : Val rT) (count : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E (Exp.open' (Exp.openRec 1 weights.fst countBody) (.lit (.int count))) Φ ⊢
      tglWp E pl(&(weightedSource weights).fst #int count) Φ :=
  twp_beta E [] (Exp.openRec 1 weights.fst countBody) (.int count) (weightedSource weights).lc Φ

private theorem twp_valid (E : CoPset) (ws : List ℕ) :
    ⊢ tglWp E pl(&(valid (rT := rT)) &(listVal natVal ws).fst)
      (fun v => iprop(⌜v = Val.bool true⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    simp only [listVal]
    iterate 8 twp_pure
    exact IH

variable [ProbLangDist.IsUniformInt rT]

/-- All arrays are private; each subsequent draw uses the preserved completed table. -/
theorem twp_aliasSamples (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (count : ℕ)
    (F : (Fin count → ℕ) → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law ws count) -∗
      tglWp E pl(&Occil.aliasSamples &(listVal natVal ws).fst #int (count : ℤ))
        (fun v => iprop(∃ ys : Fin count → ℕ,
          ⌜v = listVal natVal (List.ofFn ys)⌝ ∗ ↯ (F ys))) := by
  have hs := NeZero.pos ws.sum
  have hn := length_pos ws hs
  have hvalid := twp_valid (GF := GF) E ws
  iintro Hcredit
  rw [← source_fst]
  iapply source_beta E (listVal natVal ws) (count : ℤ)
  iapply weighted_beta E (listVal natVal ws) (count : ℤ)
  rw [opened_source (listVal natVal ws) (count : ℤ)]
  twp_bind pl(&Occil.length &(listVal natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E natVal ws
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  twp_pures
  rw [positive_test ws.length hn, positive_test ws.sum hs]
  simp only [Bool.or_false]
  twp_pure
  twp_bind pl(&(valid (rT := rT)) &(listVal natVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply hvalid
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #0))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := natVal 0) (Int.natCast_pos.mpr hn))
  iintro %work Hwork
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Hwork
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #int (ws.sum : ℤ)))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := natVal ws.sum) (Int.natCast_pos.mpr hn))
  iintro %probability Hprobability
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Hprobability
  twp_pure
  twp_bind pl(allocN(#int (ws.length : ℤ), #0))
  iapply (twp_allocN (n := (ws.length : ℤ)) (v := natVal 0) (Int.natCast_pos.mpr hn))
  iintro %aliases Haliases
  have hsetup := WalkerSetup.twp_setup (GF := GF) E work aliases ws.length ws 0
  simp only [Nat.cast_zero, add_zero] at hsetup
  isimp only [Int.toNat_natCast, ← Array.owns_replicate] at Haliases
  iterate 2 twp_pure
  twp_bind pl(&(WalkerSetup.setup (rT := rT) ws.length work aliases)
    &(listVal natVal ws).fst #0)
  iapply tglWp_wand
  isplitl [Hwork Haliases]
  · iapply hsetup
    iframe Hwork Haliases
  iintro %v ⟨%hv, Hwork, Haliases⟩
  subst v
  isimp only [initial_work ws] at Hwork
  isimp only [initial_probability ws] at Hprobability
  isimp only [initial_aliases ws] at Haliases
  iterate 3 twp_pure
  twp_bind pl(&(WalkerBalance.prepare (rT := rT) ws.length ws.sum work probability aliases) #())
  iapply tglWp_wand
  isplitl [Hwork Hprobability Haliases]
  · iapply (WalkerBalance.twp_prepare E ws.length ws.sum ws.get (weights_sum ws)
      work probability aliases (WalkerAlias.State.initial ws.get ws.sum)
      (WalkerAlias.State.valid_initial ws.get ws.sum))
    isimp only [WalkerBalance.owns]
    iframe Hwork Hprobability Haliases
  iintro %v ⟨%hv, %t, %hmass, Htable⟩
  have hrepeat := repeatSample_ownedDistSpec (GF := GF) E
    (AliasTable.owns (rT := rT) t probability aliases) (WeightedChoice.law ws) natVal
    (WalkerDraw.draw ws.length ws.sum probability aliases)
    (WalkerDraw.draw_ownedDistSpec E ws hs t hmass probability aliases) count
  subst v
  iterate 2 twp_pure
  ieval (
    change _ ⊢ tglWp E
      pl(&Occil.repeatSample
        &(WalkerDraw.draw (rT := rT) ws.length ws.sum probability aliases).fst
        #int (count : ℤ)) _)
  iapply tglWp_wand
  isplitl [Htable Hcredit]
  · iapply hrepeat.spec F (measurable_of_countable _)
    iframe Htable Hcredit
  iintro %v ⟨%ys, %hv, Htable, Hcredit⟩
  iexists ys
  iframe %hv Hcredit

/-- Nonnegative weights of positive total, with any nonnegative sample count. -/
theorem aliasSamples_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] (count : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.aliasSamples &(listVal natVal ws).fst #int (count : ℤ))
      (law ws count) (fun ys => listVal natVal (List.ofFn ys)) where
  spec F _ := wand_entails (twp_aliasSamples E ws count F)

end specification

end

end SampLib.AliasSamples
