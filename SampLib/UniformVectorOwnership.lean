import SampLib.LatentUniform

/-! # One owned world for a finite family of cached uniform streams -/

open ProbLang

namespace SampLib.UniformVector

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- All cached streams are owned together; querying a coordinate never duplicates this resource. -/
def rootsOwns : {n : ℕ} → (Fin n → Loc) → (Fin n → List Bool) → IProp GF
  | 0, _, _ => emp
  | _n + 1, roots, p => iprop(
      UniformBag.owns (roots 0) (p 0) ∗ rootsOwns (Fin.tail roots) (Fin.tail p))

private theorem tail_update_zero {α : Type} {n : ℕ} (p : Fin (n + 1) → α) (q : α) :
    Fin.tail (Function.update p 0 q) = Fin.tail p := by
  funext i
  simp [Fin.tail]

private theorem tail_update_succ {α : Type} {n : ℕ} (p : Fin (n + 1) → α)
    (i : Fin n) (q : α) :
    Fin.tail (Function.update p i.succ q) = Function.update (Fin.tail p) i q := by
  funext j
  by_cases h : j = i
  · subst j
    simp [Fin.tail]
  · have h' : j.succ ≠ i.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [Fin.tail, Function.update_of_ne h, Function.update_of_ne h']

/-- Focus one stream, retaining the continuation that reinstalls its refined prefix. -/
theorem access {n : ℕ} (roots : Fin n → Loc) (p : Fin n → List Bool) (i : Fin n) :
    rootsOwns roots p ⊢ iprop(UniformBag.owns (roots i) (p i) ∗
      ∀ q : List Bool, UniformBag.owns (roots i) q -∗ rootsOwns roots (Function.update p i q)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n IH =>
    refine Fin.cases ?_ (fun i => ?_) i
    · isimp only [rootsOwns]
      iintro ⟨Hhead, Htail⟩
      iframe Hhead
      iintro %q Hhead
      rw [tail_update_zero]
      isimp only [Function.update_self]
      iframe Hhead Htail
    · isimp only [rootsOwns]
      iintro ⟨Hhead, Htail⟩
      ihave ⟨Hi, Hrestore⟩ := IH (Fin.tail roots) (Fin.tail p) i $$ Htail
      isimp only [Fin.tail] at Hi
      iframe Hi
      iintro %q Hi
      rw [tail_update_succ]
      isimp only [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      iframe Hhead
      have hroot : Fin.tail roots i = roots i.succ := rfl
      isimp only [hroot] at Hrestore
      iapply Hrestore $$ %q Hi

end ownership

end SampLib.UniformVector
