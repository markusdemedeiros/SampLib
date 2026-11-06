import SampLib.Weighted.Support.AliasTable
import SampLib.Core.ArrayVector
import SampLib.Weighted.Laws.VoseBalance
import SampLib.Common.WeightedValidation
import SampLib.Core.Syntax.Arrays

/-! # The Vose initialization scan

The scan scales each weight into the work array and files its index on the small or
large worklist. Ownership of the five workspace locations tracks `VoseBalance.State`.
-/

open ProbLang

namespace SampLib.VoseTable

noncomputable section

/-- The initialization scan over the weight list. -/
def setup {rT : Type _} (n total : ℕ) (work aliases small large : Loc) : Exp rT := pl%
  rec fill xs index := case! xs
    | inl(v) => #()
    | inr(p) =>
      let mass := #int (n : ℤ) * fst(p);
      (#loc work +ₗ index) ← mass;
      (#loc aliases +ₗ index) ← index;
      (if mass < #int (total : ℤ) then #loc small ← inr((index, !#loc small))
        else #loc large ← inr((index, !#loc large)));
      fill (snd(p)) (index + #1)

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

abbrev encodeNat (n : ℕ) : Val rT := .int n

abbrev encodeIndex {n : ℕ} (i : Fin n) : Val rT := .int i.val

/-- Ownership of the workspace in a given preprocessing state. -/
def stateOwns {n : ℕ} (work probability aliases small large : Loc)
    (s : VoseBalance.State n) : IProp GF :=
  iprop(Array.owns work (List.ofFn (encodeNat ∘ s.work)) ∗
    Array.owns probability (List.ofFn (encodeNat ∘ s.threshold)) ∗
    Array.owns aliases (List.ofFn (encodeIndex ∘ s.target)) ∗
    appHeapFrag small (listVal encodeIndex s.small) ∗
    appHeapFrag large (listVal encodeIndex s.large))

end ownership

private theorem consecutive_tail {n : ℕ} (i : Fin n) (is : List (Fin n)) (offset : ℕ)
    (h : (i :: is).map Fin.val = List.range' offset (i :: is).length) :
    i.val = offset ∧ is.map Fin.val = List.range' (offset + 1) is.length := by
  simpa only [List.map_cons, List.length_cons, List.range'_succ, Nat.add_one_mul,
    Nat.mul_one, Nat.add_zero, List.cons.injEq] using h

theorem nat_lt_test (a b : ℕ) :
    decide ((a : ℤ) < (b : ℤ)) = decide (a < b) := by simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_setup (E : CoPset) (n total : ℕ) (weights : Fin n → ℕ)
    (work probability aliases small large : Loc) (is : List (Fin n)) (offset : ℕ)
    (hindices : is.map Fin.val = List.range' offset is.length) (s : VoseBalance.State n) :
    stateOwns (rT := rT) (GF := GF) work probability aliases small large s ⊢
      tglWp E pl(&(setup n total work aliases small large)
        &(listVal (fun i => (Val.int (weights i) : Val rT)) is).fst #int (offset : ℤ))
        (fun v : Val rT => iprop(⌜v = Val.unit⌝ ∗
          stateOwns (rT := rT) work probability aliases small large
            (VoseBalance.State.setup total weights is s))) := by
  induction is generalizing offset s with
  | nil =>
    iintro Hstate
    isimp only [VoseBalance.State.setup]
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iframe Hstate
    itrivial
  | cons i is ih =>
    obtain ⟨hhead, htail⟩ := consecutive_tail i is offset hindices
    rw [← hhead] at htail
    iintro Hstate
    isimp only [VoseBalance.State.setup]
    isimp only [stateOwns] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    rw [← hhead]
    simp only [listVal]
    iterate 8 twp_pure
    twp_bind pl((#loc work +ₗ #int (i.val : ℤ)) ← #int ((n * weights i : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_store_vector E work encodeNat
        s.work i (n * weights i)) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    twp_pure
    twp_bind pl((#loc aliases +ₗ #int (i.val : ℤ)) ← #int (i.val : ℤ))
    iapply tglWp_wand
    isplitl [Haliases]
    · iapply (Array.twp_store_vector E aliases encodeIndex s.target i i) $$ Haliases
    iintro %v ⟨%hv, Haliases⟩
    subst v
    iterate 2 twp_pure
    rw [← Nat.cast_mul, nat_lt_test]
    by_cases hsmall : n * weights i < total
    · rw [decide_eq_true hsmall]
      twp_pure
      twp_bind pl(!#loc small)
      iapply twp_load
      iframe Hsmall
      iintro Hsmall
      twp_bind (Exp.store pl(#loc small) (Exp.ofVal (listVal encodeIndex (i :: s.small))))
      iapply (twp_store (v := listVal encodeIndex (i :: s.small)))
      iframe Hsmall
      iintro Hsmall
      iterate 3 twp_pure
      have hrec := ih (i.val + 1) htail (VoseBalance.State.install total weights i s)
      simp [setup, Exp.close, Exp.closeRec] at hrec
      isimp only [Exp.ofVal]
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.install, hsmall, ite_true]
      iframe Hwork Hprobability Haliases Hsmall Hlarge
    · rw [decide_eq_false hsmall]
      twp_pure
      twp_bind pl(!#loc large)
      iapply twp_load
      iframe Hlarge
      iintro Hlarge
      twp_bind (Exp.store pl(#loc large) (Exp.ofVal (listVal encodeIndex (i :: s.large))))
      iapply (twp_store (v := listVal encodeIndex (i :: s.large)))
      iframe Hlarge
      iintro Hlarge
      iterate 3 twp_pure
      have hrec := ih (i.val + 1) htail (VoseBalance.State.install total weights i s)
      simp [setup, Exp.close, Exp.closeRec] at hrec
      isimp only [Exp.ofVal]
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.install, hsmall, ite_false]
      iframe Hwork Hprobability Haliases Hsmall Hlarge

end specification

end

end SampLib.VoseTable
