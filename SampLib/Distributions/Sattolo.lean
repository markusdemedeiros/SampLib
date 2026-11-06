module

public import SampLib.Distributions.Permutations
public import Mathlib.GroupTheory.Perm.Cycle.Basic

@[expose] public section

/-! # Uniform full cycles and Sattolo insertion

Inserting a new position into an existing cycle chooses its image among the old
positions. Removing that position reverses the operation. Empty and singleton
permutations use the identity convention of the program.
-/

open Equiv MeasureTheory Measure
open scoped ENNReal Classical

namespace SampLib.SattoloLaw

noncomputable section

/-- Every position belongs to the same orbit, including the empty convention. -/
def FullCycle {α : Type*} (σ : Perm α) : Prop := ∀ x y, σ.SameCycle x y

theorem fullCycle_iff_isCycleOn {α : Type*} (σ : Perm α) :
    FullCycle σ ↔ σ.IsCycleOn Set.univ := by
  constructor
  · intro h
    exact ⟨σ.bijOn (by simp), fun x _ y _ => h x y⟩
  · intro h x y
    exact h.2 (by trivial) (by trivial)

/-- A map preserving orbit edges preserves every finite-permutation orbit. -/
private theorem sameCycle_map {α β : Type*} [Finite α] (σ : Perm α) (τ : Perm β)
    (f : α → β) (hstep : ∀ x, τ.SameCycle (f x) (f (σ x))) {x y : α}
    (h : σ.SameCycle x y) : τ.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Perm.SameCycle.rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (hstep ((σ ^ n) x))

theorem fullCycle_permCongr {α β : Type*} [Finite α] [Finite β]
    (e : α ≃ β) (σ : Perm α) : FullCycle (Equiv.permCongr e σ) ↔ FullCycle σ := by
  constructor
  · intro h x y
    have hm := sameCycle_map (Equiv.permCongr e σ) σ e.symm
      (fun z => by simpa using
        (Perm.SameCycle.rfl : σ.SameCycle (e.symm z) (e.symm z)).apply_right)
      (h (e x) (e y))
    simpa using hm
  · intro h x y
    have hm := sameCycle_map σ (Equiv.permCongr e σ) e
      (fun z => by simpa using
        (Perm.SameCycle.rfl : (Equiv.permCongr e σ).SameCycle (e z) (e z)).apply_right)
      (h (e.symm x) (e.symm y))
    simpa using hm

private def insertOption {α : Type*} [DecidableEq α] (j : α) (σ : Perm α) :
    Perm (Option α) := Equiv.swap none (some j) * σ.optionCongr

@[simp] private theorem insertOption_none {α : Type*} [DecidableEq α]
    (j : α) (σ : Perm α) : insertOption j σ none = some j := by simp [insertOption]

private theorem insertOption_some {α : Type*} [DecidableEq α]
    (j : α) (σ : Perm α) (x : α) :
    insertOption j σ (some x) = if σ x = j then none else some (σ x) := by
  by_cases h : σ x = j <;> simp [insertOption, Equiv.swap_apply_def, h]

/-- Joining a fresh fixed position to an orbit preserves and reflects transitivity. -/
private theorem fullCycle_insertOption {α : Type*} [Finite α] [DecidableEq α]
    (j : α) (σ : Perm α) : FullCycle (insertOption j σ) ↔ FullCycle σ := by
  let τ := insertOption j σ
  have hjoin : τ.SameCycle none (some j) := ⟨1, by simp [τ]⟩
  have hembed : ∀ x, τ.SameCycle (some x) (some (σ x)) := by
    intro x
    have hx : τ.SameCycle (some x) (τ (some x)) := Perm.SameCycle.rfl.apply_right
    by_cases h : σ x = j
    · have hx' : τ.SameCycle (some x) none := by
        simpa [τ, insertOption_some, h] using hx
      simpa [h] using hx'.trans hjoin
    · simpa [τ, insertOption_some, h] using hx
  constructor
  · intro h x y
    have hcollapse : ∀ z, σ.SameCycle (z.getD j) ((τ z).getD j) := by
      intro z
      cases z with
      | none => simpa [τ] using (Perm.SameCycle.rfl : σ.SameCycle j j)
      | some z =>
        have hzcycle : σ.SameCycle z (σ z) := Perm.SameCycle.rfl.apply_right
        by_cases hz : σ z = j <;> simpa [τ, insertOption_some, hz] using hzcycle
    simpa using sameCycle_map τ σ (fun z => z.getD j) hcollapse (h (some x) (some y))
  · intro h x y
    have hall : ∀ z, τ.SameCycle none z := by
      intro z
      cases z with
      | none => exact Perm.SameCycle.rfl
      | some z => exact hjoin.trans (sameCycle_map σ τ some hembed (h j z))
    exact (hall x).symm.trans (hall y)

/-- Insert the last position into a smaller cycle by selecting its old image. -/
def insertPerm (n : ℕ) (j : Fin n) (σ : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  (Permutations.decomposeLast n).symm (j.castSucc, σ)

theorem fullCycle_insert (n : ℕ) (j : Fin n) (σ : Perm (Fin n)) :
    FullCycle (insertPerm n j σ) ↔ FullCycle σ := by
  rw [← fullCycle_permCongr finSuccEquivLast]
  have he : Equiv.permCongr finSuccEquivLast (insertPerm n j σ) = insertOption j σ := by
    ext x
    simp [insertPerm, Permutations.decomposeLast, insertOption, Equiv.permCongr_apply]
  rw [he]
  exact fullCycle_insertOption j σ

/-- The mathematical output consists of a single full position cycle. -/
abbrev Cycle (n : ℕ) := {σ : Perm (Fin n) // FullCycle σ}

instance (n : ℕ) : Fintype (Cycle n) :=
  inferInstanceAs (Fintype {σ : Perm (Fin n) // FullCycle σ})

instance (n : ℕ) : MeasurableSpace (Cycle n) := ⊤
instance (n : ℕ) : MeasurableSingletonClass (Cycle n) := ⟨fun _ => trivial⟩

/-- Add the fresh last position to a full cycle. -/
def insert {n : ℕ} (j : Fin n) (σ : Cycle n) : Cycle (n + 1) :=
  ⟨insertPerm n j σ.val, (fullCycle_insert n j σ.val).mpr σ.property⟩

@[simp] theorem insert_val {n : ℕ} (j : Fin n) (σ : Cycle n) :
    (insert j σ).val = (Permutations.decomposeLast n).symm (j.castSucc, σ.val) := rfl

private theorem decomposeLast_fst (n : ℕ) (σ : Perm (Fin (n + 1))) :
    (Permutations.decomposeLast n σ).1 = σ (Fin.last n) := by
  simpa only [Prod.eta, Equiv.symm_apply_apply] using
    (Permutations.decomposeLast_symm_last n (Permutations.decomposeLast n σ).1
      (Permutations.decomposeLast n σ).2).symm

private theorem last_image_lt (n : ℕ) (hn : 0 < n) (σ : Cycle (n + 1)) :
    (σ.val (Fin.last n)).val < n := by
  have hb := (σ.val (Fin.last n)).isLt
  by_contra h
  have hfix : σ.val (Fin.last n) = Fin.last n := Fin.ext (by simp; omega)
  have heq := (σ.property (Fin.last n) (⟨0, hn⟩ : Fin n).castSucc).eq_of_left hfix
  have hn0 := congrArg Fin.val heq
  change n = 0 at hn0
  omega

theorem insert_injective (n : ℕ) :
    Function.Injective (fun p : Fin n × Cycle n => insert p.1 p.2) := by
  intro p q h
  have hv := congrArg Subtype.val h
  change (Permutations.decomposeLast n).symm (p.1.castSucc, p.2.val) =
    (Permutations.decomposeLast n).symm (q.1.castSucc, q.2.val) at hv
  have hp := (Permutations.decomposeLast n).symm.injective hv
  exact Prod.ext (Fin.castSucc_injective n (congrArg Prod.fst hp))
    (Subtype.ext (congrArg Prod.snd hp))

theorem insert_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun p : Fin n × Cycle n => insert p.1 p.2) := by
  intro σ
  let j : Fin n := ⟨(σ.val (Fin.last n)).val, last_image_lt n hn σ⟩
  let τ := (Permutations.decomposeLast n σ.val).2
  have hj : j.castSucc = (Permutations.decomposeLast n σ.val).1 := by
    rw [decomposeLast_fst]
    rfl
  have hi : insertPerm n j τ = σ.val := by
    unfold insertPerm
    rw [hj]
    exact (Permutations.decomposeLast n).symm_apply_apply σ.val
  have ht : FullCycle τ := (fullCycle_insert n j τ).mp (by rw [hi]; exact σ.property)
  exact ⟨(j, ⟨τ, ht⟩), Subtype.ext hi⟩

/-- A full cycle is an old full cycle with the fresh position inserted at one old image. -/
def insertionEquiv (n : ℕ) (hn : 0 < n) : Fin n × Cycle n ≃ Cycle (n + 1) :=
  Equiv.ofBijective (fun p => insert p.1 p.2) ⟨insert_injective n, insert_surjective n hn⟩

@[simp] theorem insertionEquiv_apply (n : ℕ) (hn : 0 < n) (p : Fin n × Cycle n) :
    insertionEquiv n hn p = insert p.1 p.2 := rfl

def emptyCycle : Cycle 0 := ⟨1, fun x => Fin.elim0 x⟩

def singletonCycle : Cycle 1 :=
  ⟨1, fun x y => (Subsingleton.elim x y).sameCycle _⟩

@[simp] theorem emptyCycle_val : emptyCycle.val = Equiv.refl _ := rfl

@[simp] theorem singletonCycle_val : singletonCycle.val = Equiv.refl _ := rfl

instance (n : ℕ) : Nonempty (Cycle n) := by
  induction n with
  | zero => exact ⟨emptyCycle⟩
  | succ n ih =>
    cases n with
    | zero => exact ⟨singletonCycle⟩
    | succ n =>
      obtain ⟨σ⟩ := ih
      exact ⟨insert (0 : Fin (n + 1)) σ⟩

/-- There are `(n-1)!` full cycles, with the empty identity counted once. -/
theorem card_cycle (n : ℕ) : Fintype.card (Cycle n) = (n - 1).factorial := by
  induction n with
  | zero =>
    let : Unique (Cycle 0) := ⟨⟨emptyCycle⟩, fun σ => Subsingleton.elim σ _⟩
    simp
  | succ n ih =>
    cases n with
    | zero =>
      let : Unique (Cycle 1) := ⟨⟨singletonCycle⟩, fun σ => Subsingleton.elim σ _⟩
      simp
    | succ n =>
      rw [← Fintype.card_congr (insertionEquiv (n + 1) (by omega)),
        Fintype.card_prod, Fintype.card_fin, ih]
      simp [Nat.factorial_succ]

/-- Uniform over full cycles, retaining the empty and singleton identity conventions. -/
def law (n : ℕ) : Measure (Cycle n) := uniformOfFinset Finset.univ

instance (n : ℕ) : IsProbabilityMeasure (law n) :=
  isProbabilityMeasure_uniformOfFinset Finset.univ_nonempty

theorem law_singleton (n : ℕ) (σ : Cycle n) :
    law n {σ} = ((n - 1).factorial : ℝ≥0∞)⁻¹ := by
  simp [law, card_cycle]

@[simp] theorem expectation_zero (F : Cycle 0 → ℝ≥0∞) :
    ∫⁻ σ, F σ ∂law 0 = F emptyCycle := by
  have hf : F = fun _ => F emptyCycle :=
    funext fun σ => congrArg F (Subsingleton.elim σ _)
  rw [hf]
  simp

@[simp] theorem expectation_one (F : Cycle 1 → ℝ≥0∞) :
    ∫⁻ σ, F σ ∂law 1 = F singletonCycle := by
  have hf : F = fun _ => F singletonCycle :=
    funext fun σ => congrArg F (Subsingleton.elim σ _)
  rw [hf]
  simp

/-- Uniform insertion preserves the full-cycle expectation, including infinite credits. -/
theorem expectation (n : ℕ) (F : Cycle (n + 2) → ℝ≥0∞) :
    ∫⁻ σ, F σ ∂law (n + 2) =
      (∑ j : Fin (n + 1), ∫⁻ σ, F (insert j σ) ∂law (n + 1)) / (n + 1 : ℕ) := by
  simp only [law, uniformOfFinset, lintegral_finsetSum_measure, lintegral_dirac,
    lintegral_smul_measure, smul_eq_mul, Finset.card_univ, card_cycle,
    Nat.add_sub_cancel_right, ← Finset.mul_sum]
  rw [← (insertionEquiv (n + 1) (by omega)).sum_comp F, Fintype.sum_prod_type]
  simp only [insertionEquiv_apply, show n + 2 - 1 = n + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  ring

end

end SampLib.SattoloLaw

