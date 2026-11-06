import SampLib.Latent.UniformVectorOwnership
import SampLib.Latent.LatentVectorSpec

/-! # Allocating a finite vector of deferred uniform streams -/

open ProbLang

namespace SampLib.UniformVector

private theorem encode_cons {rT : Type} [ProbLangℝ rT] {n : ℕ} (l : Loc)
    (roots : Fin n → Loc) :
    pl(inr(({(LatentUniform.value (rT := rT) l).fst},
      {Exp.ofVal (listVal LatentUniform.value (List.ofFn roots))}))) =
      Exp.ofVal (listVal LatentUniform.value (List.ofFn (Fin.cons l roots))) := by
  simp [Exp.ofVal, List.ofFn_succ, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Allocating a deferred uniform does not reveal any random digit. -/
theorem twp_fresh (E : CoPset) :
    ⊢ tglWp E pl(&Occil.PSRN.newUniform #())
      (fun v : Val rT => iprop(∃ l : Loc,
        ⌜v = LatentUniform.value l⌝ ∗ UniformBag.owns l [])) := by
  have hnew := LatentUniform.twp_newUniform (rT := rT) (GF := GF) E (fun _ => 0)
  simp only [DyadicPosterior.credit, MeasureTheory.lintegral_zero] at hnew
  iapply fupd_tglWp
  imod ErrorCredit.zero with Hcredit
  imodintro
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply hnew $$ Hcredit
  iintro %v ⟨Hstate, Hcredit⟩
  isimp only [LatentUniform.owns] at Hstate
  iexact Hstate

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_repeatRoots (E : CoPset) (sample : Val rT)
    (hfresh : ⊢ tglWp E pl(&sample.fst #())
      (fun v : Val rT => iprop(∃ l : Loc,
        ⌜v = LatentUniform.value l⌝ ∗ UniformBag.owns l []))) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
      (fun v : Val rT => iprop(∃ roots : Fin n → Loc,
        ⌜v = listVal LatentUniform.value (List.ofFn roots)⌝ ∗
        rootsOwns roots (fun _ => []))) := by
  induction n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    iexists Fin.elim0
    isimp only [rootsOwns]
    ipureintro
    exact ⟨rfl, trivial⟩
  | succ n IH =>
    twp_pures
    twp_bind pl(&sample.fst #())
    iapply tglWp_wand
    isplitl []
    · iapply hfresh
    iintro %v ⟨%l, %hv, Hhead⟩
    subst v
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v ⟨%roots, %hv, Htail⟩
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal LatentUniform.value (List.ofFn (Fin.cons l roots))))
    iexists Fin.cons l roots
    isimp only [rootsOwns, Fin.cons_zero, Fin.tail_cons]
    have hprefix : Fin.tail (fun _ : Fin (n + 1) => ([] : List Bool)) =
        fun _ : Fin n => ([] : List Bool) := rfl
    rw [hprefix]
    iframe Hhead Htail

private def uniformConstructor {rT : Type} : Val rT :=
  ⟨Occil.PSRN.newUniform, .lam (by is_lc), by is_lc⟩

/-- Every list entry is an actual uniform oracle with a separately owned unsampled stream. -/
theorem twp_uniformVector (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.repeatSample &Occil.PSRN.newUniform #int (n : ℤ))
      (fun v : Val rT => iprop(∃ roots : Fin n → Loc,
        ⌜v = listVal LatentUniform.value (List.ofFn roots)⌝ ∗
        rootsOwns roots (fun _ => []))) :=
  twp_repeatRoots E uniformConstructor (twp_fresh E) n

end specification

end SampLib.UniformVector
