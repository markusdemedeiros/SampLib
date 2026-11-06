import SampLib.Weighted.Laws.RationalChoice
import SampLib.Core.Syntax.ClosedExp
import Samplers.Weighted.Tables

/-! # Exact categorical sampling from rational weights

The program validates denominators, computes their product, and scales every
fraction to that common integer denominator before a verified categorical draw.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RationalChoice

noncomputable section

/-- Exact numerator/denominator pairs, with no floating-point conversion. -/
def fractionVal {rT : Type _} [ProbLangℝ rT] (p : ℕ × ℕ) : Val rT :=
  .pair (.int (p.1 : ℤ)) (.int (p.2 : ℤ))

private theorem denominator_test (d : ℕ) (hd : 0 < d) :
    decide ((d : ℤ) ≤ 0) = false := decide_eq_false (by omega)

private def denominatorTerm {rT : Type _} : Exp rT := pl%
  rec product xs := case! xs
    | inl(u) => #1
    | inr(p) =>
      let fraction := fst(p);
      if ((fst(fraction)) < #0) || ((snd(fraction)) <= #0) then fail else
        (snd(fraction)) * product (snd(p))

private def normalizeTerm {rT : Type _} (common : ℕ) : Exp rT := pl%
  rec convert xs := case! xs
    | inl(u) => inl(#())
    | inr(p) =>
      let fraction := fst(p);
      inr(((fst(fraction)) * (#int (common : ℤ) / snd(fraction)), convert (snd(p))))

private instance rationalWeights_closed {rT : Type _} :
    ClosedExp (Occil.Weighted.rationalWeights : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Weighted.rationalWeights, Exp.fv]

private instance weightedChoice_closed {rT : Type _} :
    ClosedExp (Occil.weightedChoice : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.weightedChoice, Occil.sumInts, Occil.uniformInt, Exp.fv]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_denominator (E : CoPset) (ws : List (ℕ × ℕ))
    (hden : ∀ p ∈ ws, 0 < p.2) :
    ⊢ tglWp E pl(&denominatorTerm &(listVal fractionVal ws).fst)
      (fun v => iprop(⌜v = Val.int (denominator ws : ℤ)⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons p ws ih =>
    have hp := hden p (by simp)
    have ht := ih (fun q hq => hden q (by simp [hq]))
    cases p with
    | mk a b =>
      simp only [listVal, fractionVal]
      twp_pures
      simp only [Bool.false_or]
      rw [denominator_test b hp]
      iterate 2 twp_pure
      twp_bind pl(&denominatorTerm &(listVal fractionVal ws).fst)
      iapply tglWp_wand
      isplitl []
      · iapply ht
      iintro %v %hv
      subst v
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [denominator, Nat.cast_mul]

private theorem twp_normalize (E : CoPset) (common : ℕ) (ws : List (ℕ × ℕ)) :
    ⊢ tglWp E pl(&(normalizeTerm common) &(listVal fractionVal ws).fst)
      (fun v => iprop(⌜v = listVal (fun n : ℕ => Val.int n) (normalize common ws)⌝)) := by
  induction ws with
  | nil =>
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    exact Val.ext rfl
  | cons p ws ih =>
    cases p with
    | mk a b =>
      simp only [listVal, fractionVal]
      iterate 7 twp_pure
      twp_bind pl(&(normalizeTerm common) &(listVal fractionVal ws).fst)
      iapply tglWp_wand
      isplitl []
      · iapply ih
      iintro %v %hv
      subst v
      twp_pures
      rw [← Int.natCast_div, ← Nat.cast_mul]
      simp only [Exp.ofVal]
      let result : Val rT := .inr (.pair (.int ((a * (common / b) : ℕ) : ℤ))
        (listVal (fun n : ℕ => Val.int n) (normalize common ws)))
      iapply (tglWp_value_of_toVal (Val.toVal?_fst result))
      ipureintro
      exact Val.ext rfl

private theorem twp_rationalWeights (E : CoPset) (ws : List (ℕ × ℕ))
    (hden : ∀ p ∈ ws, 0 < p.2) :
    ⊢ tglWp E pl(&Occil.Weighted.rationalWeights &(listVal fractionVal ws).fst)
      (fun v => iprop(⌜v = listVal (fun n : ℕ => Val.int n)
        (normalize (denominator ws) ws)⌝)) := by
  have hnormalize := twp_normalize (rT := rT) (GF := GF) E (denominator ws) ws
  simp [normalizeTerm, Exp.close, Exp.closeRec] at hnormalize
  iterate 2 twp_pure
  twp_bind pl(&denominatorTerm &(listVal fractionVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_denominator E ws hden
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  iapply hnormalize

variable [ProbLangDist.IsUniformInt rT]

/-- Nonnegative rational weights of positive total give exactly their normalized proportions. -/
theorem rationalChoice_distSpec (E : CoPset) (ws : List (ℕ × ℕ))
    (hden : ∀ p ∈ ws, 0 < p.2) (hs : 0 < numerators ws) :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.rationalChoice
      &(listVal fractionVal ws).fst #()) (law ws hden hs) (fun i : ℕ => Val.int (i : ℤ)) := by
  let : NeZero (normalize (denominator ws) ws).sum := ⟨(normalized_sum_pos ws hden hs).ne'⟩
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.Weighted.rationalWeights &(listVal fractionVal ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_rationalWeights E ws hden
  iintro %v %hv
  subst v
  simp only [Exp.ofVal]
  isimp only [law] at Hcredit
  iapply ((WeightedChoice.weightedChoice_distSpec E (normalize (denominator ws) ws)).wp
    F hF _) $$ Hcredit
  iintro %i Hcredit
  iexists i
  iframe Hcredit
  itrivial

end specification

end

end SampLib.RationalChoice
