import SampLib.Weighted.Support.WalkerFind
import SampLib.Core.ArrayVector
import SampLib.Weighted.Support.AliasTable
import SampLib.Weighted.Laws.WalkerAlias

/-! # Completing Walker alias tables -/

open ProbLang

namespace SampLib.WalkerBalance

open WalkerAlias WalkerAlias.State

noncomputable section

abbrev natVal {rT : Type} [ProbLangℝ rT] (n : ℕ) : Val rT := Val.int n
abbrev indexVal {rT : Type} [ProbLangℝ rT] {n : ℕ} (i : Fin n) : Val rT := Val.int i.val

def prepare {rT : Type} (n total : ℕ) (work probability aliases : Loc) : Exp rT := pl%
  rec balance u :=
    let small := &(WalkerFind.find work n total) #0 #true;
    if small < #0 then #() else
      let large := &(WalkerFind.find work n total) #0 #false;
      if large < #0 then fail else
        let smallWeight := !(#loc work +ₗ small);
        let largeWeight := !(#loc work +ₗ large);
        (#loc probability +ₗ small) ← smallWeight;
        (#loc aliases +ₗ small) ← large;
        (#loc work +ₗ large) ← (largeWeight + smallWeight - #int (total : ℤ));
        (#loc work +ₗ small) ← #int (total : ℤ);
        balance #()

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

def owns {n total : ℕ} (s : State n total) (work probability aliases : Loc) : IProp GF :=
  iprop(Array.owns work (List.ofFn (natVal ∘ s.work)) ∗
    Array.owns probability (List.ofFn (natVal ∘ s.table.threshold)) ∗
    Array.owns aliases (List.ofFn (indexVal ∘ s.table.target)))

end ownership

private theorem terminal_result {n total : ℕ} {weight : Fin n → ℕ} {s : State n total}
    (hw : ∑ i, weight i = total) (hv : Valid weight s)
    (hnone : ∀ i, ¬ WalkerFind.eligible true total (s.work i)) :
    ∀ i, s.table.mass i = n * weight i := by
  apply terminal_mass hw hv
  simpa [WalkerFind.eligible] using hnone

private theorem large_result {n total : ℕ} {weight : Fin n → ℕ} {s : State n total}
    (hw : ∑ i, weight i = total) (hv : Valid weight s) (i : Fin n)
    (hi : s.work i < total) {r : ℤ} (hr : WalkerFind.result s.work false total r) :
    ∃ j, r = (j.val : ℤ) ∧ total < s.work j := by
  rcases hr with ⟨_, hnone⟩ | ⟨j, hr, hj⟩
  · obtain ⟨j, hj⟩ := exists_large hw hv i hi
    exact (hnone j (by simpa [WalkerFind.eligible] using hj)).elim
  · exact ⟨j, hr, by simpa [WalkerFind.eligible] using hj⟩

private theorem transfer_amount (a b total : ℕ) (h : total ≤ b) :
    (b : ℤ) + a - total = ((b + a - total : ℕ) : ℤ) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Each pass preserves integer mass and strictly reduces the unfinished work. -/
theorem twp_prepare (E : CoPset) (n total : ℕ) (weight : Fin n → ℕ)
    (hw : ∑ i, weight i = total) (work probability aliases : Loc)
    (s : State n total) (hv : Valid weight s) :
    owns s work probability aliases ⊢
      tglWp E pl(&(prepare (rT := rT) n total work probability aliases) #())
        (fun v => iprop(⌜v = Val.unit⌝ ∗ ∃ t : AliasMass.Table n total,
          ⌜∀ i, t.mass i = n * weight i⌝ ∗ AliasTable.owns t probability aliases)) := by
  revert hv
  induction s using (measure (fun s : State n total => (pending s).card)).wf.induction with
  | h s IH =>
    intro hv
    have hsmall := WalkerFind.twp_find (GF := GF) E work s.work total true n 0
      (Nat.zero_add n) (WalkerFind.before_zero s.work true total)
    have hlarge := WalkerFind.twp_find (GF := GF) E work s.work total false n 0
      (Nat.zero_add n) (WalkerFind.before_zero s.work false total)
    simp only [Nat.cast_zero] at hsmall hlarge
    iintro Hstate
    isimp only [owns] at Hstate
    ihave ⟨Hwork, Hprobability, Haliases⟩ := Hstate
    iterate 2 twp_pure
    simp only [WalkerFind.find_openRec, WalkerFind.find_closeRec]
    twp_bind pl(&(WalkerFind.find work n total) #0 #true)
    iapply tglWp_wand
    isplitl [Hwork]
    · iapply hsmall $$ Hwork
    iintro %v ⟨%r, %hr, Hwork⟩
    rcases hr with ⟨hv', hr⟩
    subst v
    rcases hr with ⟨hr, hnone⟩ | ⟨i, hr, hi⟩
    · subst r
      twp_pures
      twp_value
      imodintro
      isplit
      · itrivial
      · iexists s.table
        isplit
        · ipureintro
          exact terminal_result hw hv hnone
        · isimp only [AliasTable.owns, Function.comp_def, natVal, indexVal]
          isimp only [Function.comp_def, natVal, indexVal] at Hprobability Haliases
          iframe Hprobability Haliases
    · subst r
      simp [WalkerFind.eligible] at hi
      iterate 3 twp_pure
      simp only [WalkerFind.find_openRec]
      twp_bind pl(&(WalkerFind.find work n total) #0 #false)
      iapply tglWp_wand
      isplitl [Hwork]
      · iapply hlarge $$ Hwork
      iintro %v ⟨%r, %hr, Hwork⟩
      rcases hr with ⟨hv', hr⟩
      subst v
      obtain ⟨j, hr, hj⟩ := large_result hw hv i hi hr
      subst r
      have hvalid := valid_transfer hv i j hi hj.le (hv.untouched j hj.ne')
      have hrec := IH (transfer s i j hi) (pending_transfer_lt s i j hi hj) hvalid
      simp [-List.ofFn_succ, prepare, Exp.close, Exp.closeRec] at hrec
      iterate 3 twp_pure
      twp_bind pl(!(#loc work +ₗ #int (i.val : ℤ)))
      iapply tglWp_wand
      isplitl [Hwork]
      · iapply (Array.twp_load_ofFn E work (natVal ∘ s.work) i) $$ Hwork
      iintro %v ⟨%hv', Hwork⟩
      subst v
      twp_pure
      twp_bind pl(!(#loc work +ₗ #int (j.val : ℤ)))
      iapply tglWp_wand
      isplitl [Hwork]
      · iapply (Array.twp_load_ofFn E work (natVal ∘ s.work) j) $$ Hwork
      iintro %v ⟨%hv', Hwork⟩
      subst v
      twp_pure
      twp_bind pl((#loc probability +ₗ #int (i.val : ℤ)) ← &(natVal (s.work i)).fst)
      iapply tglWp_wand
      isplitl [Hprobability]
      · iapply (Array.twp_store_vector E probability natVal s.table.threshold i (s.work i))
          $$ Hprobability
      iintro %v ⟨%hv', Hprobability⟩
      subst v
      twp_pure
      twp_bind pl((#loc aliases +ₗ #int (i.val : ℤ)) ← &(indexVal j).fst)
      iapply tglWp_wand
      isplitl [Haliases]
      · iapply (Array.twp_store_vector E aliases indexVal s.table.target i j) $$ Haliases
      iintro %v ⟨%hv', Haliases⟩
      subst v
      iterate 3 twp_pure
      rw [transfer_amount (s.work i) (s.work j) total hj.le]
      twp_bind pl((#loc work +ₗ #int (j.val : ℤ)) ←
        &(natVal (s.work j + s.work i - total)).fst)
      iapply tglWp_wand
      isplitl [Hwork]
      · iapply (Array.twp_store_vector E work natVal s.work j
          (s.work j + s.work i - total)) $$ Hwork
      iintro %v ⟨%hv', Hwork⟩
      subst v
      twp_pure
      twp_bind pl((#loc work +ₗ #int (i.val : ℤ)) ← &(natVal total).fst)
      iapply tglWp_wand
      isplitl [Hwork]
      · iapply (Array.twp_store_vector E work natVal
          (Function.update s.work j (s.work j + s.work i - total)) i total) $$ Hwork
      iintro %v ⟨%hv', Hwork⟩
      subst v
      twp_pure
      simp only [WalkerFind.find_openRec]
      iapply hrec
      isimp only [owns, transfer]
      iframe Hwork Hprobability Haliases

end specification

end

end SampLib.WalkerBalance
