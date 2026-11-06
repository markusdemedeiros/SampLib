import SampLib.Weighted.Support.VoseSetup

/-! # The Vose pairing loop

Each step fills one small column from one large column and refiles the large index.
-/

open ProbLang

namespace SampLib.VoseTable

noncomputable section

/-- The pairing loop over the small and large worklists. -/
def balance {rT : Type _} (total : ℕ)
    (work probability aliases small large : Loc) : Exp rT := pl%
  rec prepare u := case! !#loc small
    | inl(v) => #()
    | inr(s) => case! !#loc large
      | inl(v) => #()
      | inr(g) =>
        let lo := fst(s);
        let hi := fst(g);
        let mass := !(#loc work +ₗ lo);
        let remainder := !(#loc work +ₗ hi) + mass - #int (total : ℤ);
        (#loc probability +ₗ lo) ← mass;
        (#loc aliases +ₗ lo) ← hi;
        (#loc work +ₗ hi) ← remainder;
        (if remainder < #int (total : ℤ) then
          (#loc small ← inr((hi, snd(s))); #loc large ← snd(g))
        else #loc small ← snd(s));
        prepare #()

private theorem remainder_cast (a b total : ℕ) (h : total ≤ a) :
    (a : ℤ) + b - total = ((a + b - total : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_balance (E : CoPset) (n total : ℕ) (weights : Fin n → ℕ)
    (work probability aliases small large : Loc) (s : VoseBalance.State n)
    (hInv : VoseBalance.Invariant weights total s) :
    stateOwns (rT := rT) (GF := GF) work probability aliases small large s ⊢
      tglWp E pl(&(balance total work probability aliases small large) #())
        (fun v : Val rT => iprop(⌜v = Val.unit⌝ ∗
          stateOwns (rT := rT) work probability aliases small large (s.finish total))) := by
  revert hInv
  induction s using VoseBalance.State.finish.induct total with
  | case1 s hs =>
    intro hInv
    have hfinish : s.finish total = s := by rw [VoseBalance.State.finish, hs]
    iintro Hstate
    isimp [balance, Exp.close, Exp.closeRec]
    isimp only [hfinish]
    isimp only [stateOwns, hs] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iterate 2 twp_pure
    twp_bind pl(!#loc small)
    iapply twp_load
    iframe Hsmall
    iintro Hsmall
    twp_pures
    twp_value
    imodintro
    isimp only [stateOwns, hs]
    iframe Hwork Hprobability Haliases Hsmall Hlarge
  | case2 s lo ss hs hl =>
    intro hInv
    have hfinish : s.finish total = s := by rw [VoseBalance.State.finish, hs, hl]
    iintro Hstate
    isimp [balance, Exp.close, Exp.closeRec]
    isimp only [hfinish]
    isimp only [stateOwns, hs, hl] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iterate 2 twp_pure
    twp_bind pl(!#loc small)
    iapply twp_load
    iframe Hsmall
    iintro Hsmall
    iterate 2 twp_pure
    twp_bind pl(!#loc large)
    iapply twp_load
    iframe Hlarge
    iintro Hlarge
    twp_pures
    twp_value
    imodintro
    isimp only [stateOwns, hs, hl]
    iframe Hwork Hprobability Haliases Hsmall Hlarge
  | case3 s lo ss hi ls hs hl ih =>
    intro hInv
    have hnext := VoseBalance.advance_invariant weights s hInv lo hi ss ls hs hl
    have hlarge := hInv.large_le hi (by simp [hl])
    have hfinish : s.finish total = (s.advance total lo hi).finish total := by
      rw [VoseBalance.State.finish, hs, hl]
    have hrec := ih hnext
    simp [balance, Exp.close, Exp.closeRec] at hrec
    iintro Hstate
    isimp [balance, Exp.close, Exp.closeRec]
    isimp only [hfinish]
    isimp only [stateOwns, hs, hl] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases, Hsmall, Hlarge⟩ := Hstate
    iterate 2 twp_pure
    twp_bind pl(!#loc small)
    iapply twp_load
    iframe Hsmall
    iintro Hsmall
    iterate 2 twp_pure
    twp_bind pl(!#loc large)
    iapply twp_load
    iframe Hlarge
    iintro Hlarge
    iterate 6 twp_pure
    twp_bind pl(!(#loc work +ₗ #int (lo.val : ℤ)))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_load_ofFn E work (encodeNat ∘ s.work) lo) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    twp_pure
    twp_bind pl(!(#loc work +ₗ #int (hi.val : ℤ)))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_load_ofFn E work (encodeNat ∘ s.work) hi) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    iterate 3 twp_pure
    rw [remainder_cast (s.work hi) (s.work lo) total hlarge]
    twp_bind pl((#loc probability +ₗ #int (lo.val : ℤ)) ← #int (s.work lo : ℤ))
    iapply tglWp_wand
    isplitl [Hprobability]
    · iapply (Array.twp_store_vector E probability encodeNat s.threshold lo (s.work lo))
        $$ Hprobability
    iintro %v ⟨%hv, Hprobability⟩
    subst v
    twp_pure
    twp_bind pl((#loc aliases +ₗ #int (lo.val : ℤ)) ← #int (hi.val : ℤ))
    iapply tglWp_wand
    isplitl [Haliases]
    · iapply (Array.twp_store_vector E aliases encodeIndex s.target lo hi) $$ Haliases
    iintro %v ⟨%hv, Haliases⟩
    subst v
    twp_pure
    twp_bind pl((#loc work +ₗ #int (hi.val : ℤ)) ←
      #int ((s.work hi + s.work lo - total : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply (Array.twp_store_vector E work encodeNat s.work hi
        (s.work hi + s.work lo - total)) $$ Hwork
    iintro %v ⟨%hv, Hwork⟩
    subst v
    iterate 2 twp_pure
    rw [nat_lt_test]
    by_cases hr : s.work hi + s.work lo - total < total
    · rw [decide_eq_true hr]
      iterate 2 twp_pure
      twp_bind (Exp.store pl(#loc small) (Exp.ofVal (listVal encodeIndex (hi :: ss))))
      iapply (twp_store (v := listVal encodeIndex (hi :: ss)))
      iframe Hsmall
      iintro Hsmall
      iterate 2 twp_pure
      twp_bind (Exp.store pl(#loc large) (Exp.ofVal (listVal encodeIndex ls)))
      iapply (twp_store (v := listVal encodeIndex ls))
      iframe Hlarge
      iintro Hlarge
      twp_pure
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.advance, hs, hl, List.tail_cons, hr, ite_true]
      iframe Hwork Hprobability Haliases Hsmall Hlarge
    · rw [decide_eq_false hr]
      iterate 2 twp_pure
      twp_bind (Exp.store pl(#loc small) (Exp.ofVal (listVal encodeIndex ss)))
      iapply (twp_store (v := listVal encodeIndex ss))
      iframe Hsmall
      iintro Hsmall
      twp_pure
      iapply hrec
      isimp only [stateOwns, VoseBalance.State.advance, hs, hl, List.tail_cons, hr, ite_false]
      iframe Hwork Hprobability Haliases Hsmall Hlarge

end specification

end

end SampLib.VoseTable
