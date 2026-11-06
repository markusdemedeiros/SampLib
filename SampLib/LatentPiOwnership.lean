import SampLib.LatentRepresentedViews

/-! # One owned state for a finite family of deferred components -/

open ProbLang

namespace SampLib.LatentReal.PiModel

noncomputable section

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} {GF : BundledGFunctors}
local bi (IProp GF)

/-- All component resources are retained together, indexed by their actual handles. -/
def owns : {n : ℕ} → (S : Fin n → Type) →
    (∀ i, Val rT → S i → IProp GF) → (Fin n → Val rT) → (∀ i, S i) → IProp GF
  | 0, _, _, _, _ => emp
  | _ + 1, S, O, handles, s => iprop(O 0 (handles 0) (s 0) ∗
      owns (fun i => S i.succ) (fun i => O i.succ) (Fin.tail handles) (Fin.tail s))

private theorem tail_update_zero {n : ℕ} {S : Fin (n + 1) → Type}
    (s : ∀ i, S i) (q : S 0) :
    Fin.tail (Function.update s 0 q) = Fin.tail s := by
  funext i
  simp [Fin.tail]

private theorem tail_update_succ {n : ℕ} {S : Fin (n + 1) → Type}
    (s : ∀ i, S i) (i : Fin n) (q : S i.succ) :
    Fin.tail (Function.update s i.succ q) = Function.update (Fin.tail s) i q := by
  funext j
  by_cases h : j = i
  · subst j
    simp [Fin.tail]
  · have h' : j.succ ≠ i.succ := fun heq => h (Fin.succ_inj.mp heq)
    simp [Fin.tail, Function.update_of_ne h, Function.update_of_ne h']

/-- Focus one component and retain a continuation that restores its refined state. -/
theorem access {n : ℕ} (S : Fin n → Type) (O : ∀ i, Val rT → S i → IProp GF)
    (handles : Fin n → Val rT) (s : ∀ i, S i) (i : Fin n) :
    owns S O handles s ⊢ iprop(O i (handles i) (s i) ∗
      ∀ q : S i, O i (handles i) q -∗ owns S O handles (Function.update s i q)) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · isimp only [owns]
      iintro ⟨Hhead, Htail⟩
      iframe Hhead
      iintro %q Hhead
      rw [tail_update_zero]
      isimp only [Function.update_self]
      iframe Hhead Htail
    · isimp only [owns]
      iintro ⟨Hhead, Htail⟩
      ihave ⟨Hi, Hrestore⟩ := ih (fun j => S j.succ) (fun j => O j.succ)
        (Fin.tail handles) (Fin.tail s) i $$ Htail
      isimp only [Fin.tail] at Hi
      iframe Hi
      iintro %q Hi
      rw [tail_update_succ]
      isimp only [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      iframe Hhead
      have hh : Fin.tail handles i = handles i.succ := rfl
      isimp only [hh] at Hrestore
      iapply Hrestore $$ %q Hi

end ownership

end

end SampLib.LatentReal.PiModel
