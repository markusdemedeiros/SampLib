import SampLib.Core.ArrayOwnership

/-! # Initializing Walker work and alias arrays -/

open ProbLang

namespace SampLib.WalkerSetup

abbrev natVal {rT : Type} [ProbLangℝ rT] (n : ℕ) : Val rT := Val.int n

def setup {rT : Type} (n : ℕ) (work aliases : Loc) : Exp rT := pl%
  rec fill xs i := case! xs | inl(u) => #() | inr(p) =>
    ((#loc work +ₗ i) ← (#int (n : ℤ) * fst(p));
    (#loc aliases +ₗ i) ← i;
    fill (snd(p)) (i + #1))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The input initializes scaled work and identity aliases in one pass. -/
theorem twp_setup (E : CoPset) (work aliases : Loc) (n : ℕ) (xs : List ℕ) (start : ℕ) :
    iprop(Array.owns (work + (start : ℤ)) (List.replicate xs.length (natVal 0)) ∗
      Array.owns (aliases + (start : ℤ)) (List.replicate xs.length (natVal 0))) ⊢
      tglWp E pl(&(setup (rT := rT) n work aliases)
        &(listVal natVal xs).fst #int (start : ℤ))
        (fun v => iprop(⌜v = Val.unit⌝ ∗
          Array.owns (work + (start : ℤ)) (xs.map (fun w => natVal (n * w))) ∗
          Array.owns (aliases + (start : ℤ)) ((List.range' start xs.length).map natVal))) := by
  induction xs generalizing start with
  | nil =>
    iintro ⟨Hwork, Haliases⟩
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    isimp only [List.length_nil, List.map_nil, List.range'_zero]
    isimp only [List.length_nil, List.replicate_zero] at Hwork Haliases
    isplit
    · itrivial
    · isplitl [Hwork]
      · iexact Hwork
      · iexact Haliases
  | cons x xs IH =>
    iintro ⟨Hwork, Haliases⟩
    isimp only [List.length_cons, List.replicate_succ, Array.owns] at Hwork Haliases
    ihave ⟨Hhead, Htail⟩ := Hwork
    ihave ⟨Hindex, Hindices⟩ := Haliases
    simp only [listVal]
    twp_pures
    twp_bind (Exp.store pl(#loc (work + (start : ℤ))) (Exp.ofVal (natVal (n * x))))
    iapply twp_store
    iframe Hhead
    iintro Hhead
    twp_pures
    twp_bind (Exp.store pl(#loc (aliases + (start : ℤ))) (Exp.ofVal (natVal start)))
    iapply twp_store
    iframe Hindex
    iintro Hindex
    iterate 3 twp_pure
    rw [← Nat.cast_add_one]
    have hrec := IH (start + 1)
    simp [setup, Exp.close, Exp.closeRec] at hrec
    simp only [Nat.cast_add_one, Exp.ofVal]
    iapply tglWp_wand
    isplitl [Htail Hindices]
    · iapply hrec
      isimp only [add_assoc] at Htail Hindices
      iframe Htail Hindices
    iintro %v ⟨%hv, Htail, Hindices⟩
    iframe %hv
    isimp only [List.map_cons, List.length_cons, List.range'_succ, List.map_cons,
      Array.owns, Nat.cast_add_one, add_assoc]
    iframe Hhead Hindex Htail Hindices

end specification

end SampLib.WalkerSetup
