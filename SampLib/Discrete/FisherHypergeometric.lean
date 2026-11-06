import SampLib.Discrete.Laws.FisherHypergeometric
import SampLib.Discrete.Support.IntegerChoose
import SampLib.Discrete.Support.IntegerPower
import SampLib.Core.Syntax.ClosedExp
import Samplers.Discrete.Urns
import Metrology.Iris.LocalBI

/-! # Fisher sampling by exact finite weights

Construct the standard Fisher weights with exact integer arithmetic, then invoke
the verified categorical sampler. The combinatorial law lives in the companion
mathematical file; the program proof only builds and samples its weight table.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.FisherHypergeometric

noncomputable section

private instance choose_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.choose : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.choose, Exp.fv]

private instance power_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.integerPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.integerPower, Exp.fv]

private instance weighted_closed {rT : Type _} :
    ClosedExp (Occil.weightedChoice : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.weightedChoice, Occil.sumInts, Exp.fv, UniformInt.uniformInt_fv]

private def weightExpr {rT : Type _} (n ones zeros a b k : ℕ) : Exp rT := pl%
  &Occil.DiscreteExtra.choose #int (ones : ℤ) #int (k : ℤ) *
    &Occil.DiscreteExtra.choose #int (zeros : ℤ) (#int (n : ℤ) - #int (k : ℤ)) *
    &Occil.DiscreteExtra.integerPower #int (a : ℤ) #int (k : ℤ) *
    &Occil.DiscreteExtra.integerPower #int (b : ℤ) (#int (n : ℤ) - #int (k : ℤ))

private def build {rT : Type _} (n ones zeros a b : ℕ) : Exp rT := pl%
  rec weights k := if #int (n : ℤ) < k then inl(#()) else
    let w := &Occil.DiscreteExtra.choose #int (ones : ℤ) k *
      &Occil.DiscreteExtra.choose #int (zeros : ℤ) (#int (n : ℤ) - k) *
      &Occil.DiscreteExtra.integerPower #int (a : ℤ) k *
      &Occil.DiscreteExtra.integerPower #int (b : ℤ) (#int (n : ℤ) - k);
    inr((w, weights (k + #1)))

private def tableFrom (n ones zeros a b start length : ℕ) : List ℕ :=
  (List.range' start length).map (weight n ones zeros a b)

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (n : ℕ) (ns : List ℕ) :
    pl(inr((#int (n : ℤ), {Exp.ofVal (listVal (fun k : ℕ => Val.int (k : ℤ)) ns)}))) =
      Exp.ofVal (listVal (fun k : ℕ => Val.int (k : ℤ)) (n :: ns) : Val rT) := by
  simp [Exp.ofVal, listVal]

private theorem sub_cast (n k : ℕ) (hk : k ≤ n) :
    (n : ℤ) - k = ((n - k : ℕ) : ℤ) := (Nat.cast_sub hk).symm

private theorem power_cast (a k : ℕ) : (a : ℤ) ^ k = ((a ^ k : ℕ) : ℤ) := by
  norm_cast

private theorem build_test (n k : ℕ) : decide ((n : ℤ) < k) = decide (n < k) :=
  decide_eq_decide.mpr (by omega)

private theorem tableFrom_zero (n ones zeros a b : ℕ) :
    tableFrom n ones zeros a b 0 (n + 1) = table n ones zeros a b := by
  simp [tableFrom, table, List.range_eq_range']

private theorem guard_test (n ones zeros a b : ℕ) (hn : n ≤ ones + zeros)
    (ha : 0 < a) (hb : 0 < b) :
    Bool.or (Bool.or (Bool.or false
      (decide ((ones : ℤ) + zeros < n))) (decide ((a : ℤ) ≤ 0)))
      (decide ((b : ℤ) ≤ 0)) = false := by
  simp [show ¬(ones : ℤ) + zeros < n by omega, Nat.ne_of_gt ha, Nat.ne_of_gt hb]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_weight (E : CoPset) (n ones zeros a b k : ℕ) (hk : k ≤ n) :
    ⊢ tglWp E (weightExpr n ones zeros a b k)
      (fun v : Val rT => iprop(⌜v = Val.int (weight n ones zeros a b k : ℤ)⌝)) := by
  twp_pure
  rw [sub_cast n k hk]
  twp_bind pl(&Occil.DiscreteExtra.integerPower #int (b : ℤ) #int ((n - k : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerPower E b (n - k)
  iintro %v %hv
  subst v
  rw [power_cast]
  twp_bind pl(&Occil.DiscreteExtra.integerPower #int (a : ℤ) #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerPower E a k
  iintro %v %hv
  subst v
  rw [power_cast]
  twp_pure
  rw [sub_cast n k hk]
  twp_bind pl(&Occil.DiscreteExtra.choose #int (zeros : ℤ) #int ((n - k : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerChoose E zeros (n - k)
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.DiscreteExtra.choose #int (ones : ℤ) #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerChoose E ones k
  iintro %v %hv
  subst v
  iterate 3 twp_pure
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]
  twp_value
  imodintro
  ipureintro
  rfl

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_build (E : CoPset) (n ones zeros a b fuel start : ℕ)
    (h : start + fuel = n + 1) :
    ⊢ tglWp E pl(&(build n ones zeros a b) #int (start : ℤ))
      (fun v : Val rT => iprop(⌜v = listVal (fun k : ℕ => Val.int (k : ℤ))
        (tableFrom n ones zeros a b start fuel)⌝)) := by
  induction fuel generalizing start with
  | zero =>
    have hs : n < start := by omega
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    rw [build_test n start, decide_eq_true hs]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [tableFrom, listVal]
  | succ fuel ih =>
    have hs : start ≤ n := by omega
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    rw [build_test n start, decide_eq_false (Nat.not_lt.mpr hs)]
    twp_pure
    twp_bind (weightExpr n ones zeros a b start)
    iapply tglWp_wand
    isplitl []
    · iapply twp_weight E n ones zeros a b start hs
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&(build n ones zeros a b) #int ((start + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply ih (start + 1) (by omega)
    iintro %v %hv
    subst v
    rw [encode_cons]
    iapply tglWp_value
    ipureintro
    simp [tableFrom, List.range'_succ, listVal]

/-- Construct and sample the exact integer Fisher weights. -/
theorem twp_fisherHypergeometric (E : CoPset) (n ones zeros a b : ℕ)
    (hn : n ≤ ones + zeros) (ha : 0 < a) (hb : 0 < b) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n ones zeros a b) -∗
      tglWp E pl(&Occil.DiscreteExtra.fisherHypergeometric #int (n : ℤ)
        #int (ones : ℤ) #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  have ht := total_pos n ones zeros a b hn ha hb
  let _ : NeZero (table n ones zeros a b).sum := ⟨Nat.ne_of_gt ht⟩
  iintro Hcredit
  twp_pures
  rw [guard_test n ones zeros a b hn ha hb]
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&(build n ones zeros a b) #0)
  iapply tglWp_wand
  isplitl []
  · have h := twp_build (rT := rT) (GF := GF) E n ones zeros a b (n + 1) 0 (by omega)
    simp only [tableFrom_zero] at h
    iapply h
  iintro %v %hv
  subst v
  isimp only [law, ite_eq_left ht] at Hcredit
  simp only [Exp.ofVal]
  iapply (WeightedChoice.weightedChoice_distSpec E (table n ones zeros a b)).spec F
    (measurable_of_countable _) $$ Hcredit

/-- Typed Fisher noncentral hypergeometric law, including empty and exhausted draws. -/
theorem fisherHypergeometric_distSpec (E : CoPset) (n ones zeros a b : ℕ)
    (hn : n ≤ ones + zeros) (ha : 0 < a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.fisherHypergeometric #int (n : ℤ)
      #int (ones : ℤ) #int (zeros : ℤ) #int (a : ℤ) #int (b : ℤ))
      (law n ones zeros a b) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_fisherHypergeometric E n ones zeros a b hn ha hb F)

end specification


end

end SampLib.FisherHypergeometric
