import SampLib.PSRN.Support.UniformVectorAllocation
import SampLib.Latent.UniformVectorModel
import SampLib.PSRN.Support.LatentUniformRoot

/-! # Jointly observable vectors of deferred uniforms

Allocation creates the actual list of memoized handles. Each observation focuses
one stream while retaining the entire world and its joint posterior credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformVector

noncomputable section

private theorem vectorVal_roots {rT : Type} [ProbLangℝ rT] {n : ℕ} (roots : Fin n → Loc) :
    LatentReal.vectorVal (fun i => LatentUniform.value (rT := rT) (roots i)) =
      listVal LatentUniform.value (List.ofFn roots) := by
  induction n with
  | zero => rfl
  | succ n IH =>
    have htail : Fin.tail roots = fun i => roots i.succ := rfl
    simpa only [LatentReal.vectorVal, List.ofFn_succ, listVal, id_eq, htail] using
      congrArg (fun v : Val rT => Val.inr (Val.pair (LatentUniform.value (roots 0)) v))
        (IH (Fin.tail roots))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The handles are exactly the closures backed by the jointly owned cached streams. -/
def owns {n : ℕ} (handles : Fin n → Val rT) (p : Fin n → List Bool) : IProp GF :=
  iprop(∃ roots : Fin n → Loc,
    ⌜handles = fun i => LatentUniform.value (roots i)⌝ ∗ rootsOwns roots p)

/-- A coordinate read exposes its exact prefix while retaining all owned streams. -/
theorem twp_observe_coordinate (E : CoPset) {n : ℕ} (roots : Fin n → Loc)
    (p : Fin n → List Bool) (i : Fin n) (bits : ℕ)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    iprop(rootsOwns roots p ∗ ↯ (∫⁻ x, F x ∂law p)) ⊢
      tglWp E pl(&(LatentUniform.value (rT := rT) (roots i)).fst #int (bits : ℤ))
        (fun result : Val rT => iprop(∃ q : List Bool,
          ⌜UniformBag.readRefines (p i) bits q ∧
            result = intervalVal (LatentUniform.interval q bits)⌝ ∗
          rootsOwns roots (Function.update p i q) ∗
          ↯ (∫⁻ x, F x ∂law (Function.update p i q)))) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hread := LatentUniform.twp_observe_root (rT := rT) (GF := GF) E
      (roots i) (p i) bits (coordinateCredit p i F) (measurable_coordinateCredit p i hF)
    unfold DyadicPosterior.credit at hread
    iintro ⟨Hroots, Hcredit⟩
    isimp only [expectation_coordinate p i F hF] at Hcredit
    ihave ⟨Hstream, Hrestore⟩ := access roots p i $$ Hroots
    iapply tglWp_wand
    isplitl [Hstream Hcredit]
    · iapply hread
      iframe Hstream Hcredit
    iintro %result ⟨%q, %hq, Hstream, Hcredit⟩
    isimp only [← expectation_update p i q F hF] at Hcredit
    ihave Hroots := Hrestore $$ %q Hstream
    iexists q
    iframe Hroots Hcredit
    ipureintro
    exact hq

/-- Any coordinate can be read while preserving the one shared world. -/
theorem coordinateSpec (E : CoPset) {n : ℕ} (handles : Fin n → Val rT) (i : Fin n) :
    IsViewSpec (GF := GF) E (view i) (owns handles) (handles i) where
  observe v p bits F hF := by
    iintro ⟨Hview, Hcredit⟩
    isimp only [ViewOwns] at Hview
    icases Hview with ⟨%hv, Hworld⟩
    subst v
    isimp only [owns] at Hworld
    ihave ⟨%roots, %hhandles, Hroots⟩ := Hworld
    subst handles
    isimp only [view, world] at Hcredit
    iapply tglWp_wand
    isplitl [Hroots Hcredit]
    · iapply twp_observe_coordinate E roots p i bits F hF
      iframe Hroots Hcredit
    iintro %result ⟨%q, %hq, Hroots, Hcredit⟩
    rcases hq with ⟨hprefix, rfl⟩
    ihave Hstate : owns (fun i => LatentUniform.value (roots i)) (Function.update p i q)
      $$ [Hroots]
    · isimp only [owns]
      iexists roots
      iframe Hroots
      itrivial
    iexists Function.update p i q, LatentUniform.interval q bits
    rw [show (view i).posterior (Function.update p i q) = law (Function.update p i q) from rfl]
    isimp only [ViewOwns]
    iframe Hstate Hcredit
    ipureintro
    exact ⟨trivial, refines_update p i q hprefix.1, view_interval_encloses p i q bits hprefix⟩

/-- The actual repeated constructor represents an independent uniform vector, jointly. -/
theorem uniformVector_latentSpec (E : CoPset) (n : ℕ) :
    IsLatentVectorSpec (GF := GF) E pl(&Occil.repeatSample &Occil.PSRN.newUniform #int (n : ℤ))
      (world n) (fun i => view i) (initial n) owns where
  sameWorld := view_sameWorld
  coordinate := coordinateSpec E
  payload := {
    spec := fun F _ => by
      iintro Hcredit
      iapply tglWp_wand
      isplitl []
      · iapply twp_uniformVector E n
      iintro %v ⟨%roots, %hv, Hroots⟩
      iexists initial n
      iframe Hcredit
      isplitl []
      · ipureintro
        exact (world n).refines_refl _
      isimp only [VectorOwns]
      iexists fun i => LatentUniform.value (roots i)
      isplitl []
      · ipureintro
        exact hv.trans (vectorVal_roots roots).symm
      isimp only [owns, initial]
      iexists roots
      isplitl []
      · ipureintro
        rfl
      have hinit : rootsOwns (rT := rT) (GF := GF) roots (initial n) =
          rootsOwns roots (fun _ : Fin n => []) := rfl
      rw [hinit]
      iexact Hroots
      }

end specification

end

end SampLib.UniformVector
