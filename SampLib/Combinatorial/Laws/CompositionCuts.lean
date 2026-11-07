module

public import SampLib.Combinatorial.Laws.IntegerRange
public import Mathlib.Data.List.Sublists
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Interior cuts and the gaps between them

Consecutive gaps biject strictly increasing interior cut lists with positive
compositions. Enumerating the cut sublists lists every positive composition once.
-/

open scoped Classical

namespace SampLib.Compositions

noncomputable section

/-- Consecutive gaps, including the final gap to the right endpoint. -/
def gaps (total prev : ℤ) : List ℤ → List ℤ
  | [] => [total - prev]
  | x :: xs => (x - prev) :: gaps total x xs

/-- Positive ordered parts of a prescribed length and total. -/
def positive (n total : ℕ) (parts : List ℤ) : Prop :=
  parts.length = n ∧ (∀ x ∈ parts, 0 < x) ∧ parts.sum = (total : ℤ)

/-- Recover the interior partial sums, omitting the final endpoint. -/
def cutPoints (prev : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: xs => if xs = [] then [] else (prev + x) :: cutPoints (prev + x) xs

@[simp] theorem gaps_length (total prev : ℤ) (cuts : List ℤ) :
    (gaps total prev cuts).length = cuts.length + 1 := by
  induction cuts generalizing prev with
  | nil => rfl
  | cons x xs ih => simp [gaps, ih]

@[simp] theorem gaps_sum (total prev : ℤ) (cuts : List ℤ) :
    (gaps total prev cuts).sum = total - prev := by
  induction cuts generalizing prev with
  | nil => simp [gaps]
  | cons x xs ih => simp only [gaps, List.sum_cons, ih]; omega

theorem gaps_ne_nil (total prev : ℤ) (cuts : List ℤ) : gaps total prev cuts ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

@[simp] theorem cutPoints_gaps (total prev : ℤ) (cuts : List ℤ) :
    cutPoints prev (gaps total prev cuts) = cuts := by
  induction cuts generalizing prev with
  | nil => simp [gaps, cutPoints]
  | cons x xs ih =>
    simp only [gaps, cutPoints, gaps_ne_nil, ite_false]
    rw [show prev + (x - prev) = x by omega, ih]

theorem gaps_injective (total prev : ℤ) : Function.Injective (gaps total prev) := by
  intro xs ys h
  simpa using congrArg (cutPoints prev) h

@[simp] theorem cutPoints_length (prev : ℤ) (parts : List ℤ) :
    (cutPoints prev parts).length = parts.length - 1 := by
  induction parts generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp [cutPoints]
    | cons y ys =>
      rw [cutPoints]
      simp only [List.cons_ne_nil, ite_false, List.length_cons]
      rw [ih]
      simp only [List.length_cons]
      omega

theorem gaps_cutPoints (total prev : ℤ) (parts : List ℤ) (hne : parts ≠ [])
    (hs : parts.sum = total - prev) : gaps total prev (cutPoints prev parts) = parts := by
  induction parts generalizing prev with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => simpa [gaps, cutPoints] using hs.symm
    | cons y ys =>
      have ht : (y :: ys).sum = total - (prev + x) := by
        simp only [List.sum_cons] at hs ⊢
        omega
      rw [cutPoints]
      simp only [List.cons_ne_nil, ite_false]
      rw [gaps, show prev + x - prev = x by omega, ih (prev + x) (by simp) ht]

/-- Strictly increasing cuts between the two endpoints. -/
def within (prev total : ℤ) : List ℤ → Prop
  | [] => prev < total
  | x :: xs => prev < x ∧ within x total xs

theorem within_bounds (prev total : ℤ) (cuts : List ℤ) (h : within prev total cuts) :
    prev < total ∧ ∀ x ∈ cuts, prev < x ∧ x < total := by
  induction cuts generalizing prev with
  | nil => exact ⟨h, by simp⟩
  | cons x xs ih =>
    obtain ⟨hpx, htail⟩ := h
    obtain ⟨hxt, hb⟩ := ih x htail
    refine ⟨hpx.trans hxt, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hpx, hxt⟩
    · exact ⟨hpx.trans (hb y hy).1, (hb y hy).2⟩

theorem within_mono_left {prev next total : ℤ} {cuts : List ℤ}
    (h : within next total cuts) (hp : prev ≤ next) : within prev total cuts := by
  cases cuts with
  | nil => exact hp.trans_lt h
  | cons x xs => exact ⟨hp.trans_lt h.1, h.2⟩

theorem within_sublist {xs ys : List ℤ} (h : xs.Sublist ys) {prev total : ℤ}
    (hy : within prev total ys) : within prev total xs := by
  induction h generalizing prev with
  | slnil => exact hy
  | cons x h ih => exact within_mono_left (ih hy.2) hy.1.le
  | cons_cons x h ih => exact ⟨hy.1, ih hy.2⟩

theorem gaps_positive (total prev : ℤ) (cuts : List ℤ) :
    (∀ x ∈ gaps total prev cuts, 0 < x) ↔ within prev total cuts := by
  induction cuts generalizing prev with
  | nil => simp [gaps, within]
  | cons x xs ih => simp [gaps, within, ih]

theorem cutPoints_within (total prev : ℤ) (parts : List ℤ) (hne : parts ≠ [])
    (hp : ∀ x ∈ parts, 0 < x) (hs : parts.sum = total - prev) :
    within prev total (cutPoints prev parts) := by
  induction parts generalizing prev with
  | nil => contradiction
  | cons x xs ih =>
    have hx := hp x (by simp)
    cases xs with
    | nil =>
      simp only [List.sum_cons, List.sum_nil, add_zero] at hs
      simpa [cutPoints, within] using (by omega : prev < total)
    | cons y ys =>
      have ht : (y :: ys).sum = total - (prev + x) := by
        simp only [List.sum_cons] at hs ⊢
        omega
      simp only [cutPoints, List.cons_ne_nil, ite_false, within]
      exact ⟨by omega, ih (prev + x) (by simp) (fun z hz => hp z (by simp [hz])) ht⟩

theorem interval_length (lo : ℤ) (n : ℕ) : (IntegerRange.interval lo n).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih => simp [IntegerRange.interval, ih]

theorem interval_within (lo : ℤ) (n : ℕ) :
    within (lo - 1) (lo + n) (IntegerRange.interval lo n) := by
  induction n generalizing lo with
  | zero => simp [IntegerRange.interval, within]
  | succ n ih =>
    change lo - 1 < lo ∧ within lo (lo + ((n + 1 : ℕ) : ℤ))
      (IntegerRange.interval (lo + 1) n)
    refine ⟨by omega, ?_⟩
    have he : lo + ((n + 1 : ℕ) : ℤ) = (lo + 1) + n := by push_cast; ring
    rw [he]
    simpa using ih (lo + 1)

theorem within_nodup (prev total : ℤ) (cuts : List ℤ) (h : within prev total cuts) :
    cuts.Nodup := by
  induction cuts generalizing prev with
  | nil => simp
  | cons x xs ih =>
    refine List.nodup_cons.mpr ⟨?_, ih x h.2⟩
    intro hx
    have := (within_bounds x total xs h.2).2 x hx
    omega

theorem sublist_interval_of_within (lo : ℤ) (n : ℕ) (cuts : List ℤ)
    (h : within (lo - 1) (lo + n) cuts) : cuts.Sublist (IntegerRange.interval lo n) := by
  induction n generalizing lo cuts with
  | zero =>
    cases cuts with
    | nil => simp
    | cons x xs =>
      have hb := (within_bounds (lo - 1) (lo + 0) (x :: xs) h).2 x (by simp)
      omega
  | succ n ih =>
    cases cuts with
    | nil => simp
    | cons x xs =>
      have hb := (within_bounds (lo - 1) (lo + ((n + 1 : ℕ) : ℤ)) (x :: xs) h).2 x
        (by simp)
      have he : lo + ((n + 1 : ℕ) : ℤ) = (lo + 1) + n := by push_cast; ring
      by_cases hx : x = lo
      · subst x
        apply List.Sublist.cons_cons
        apply ih (lo + 1) xs
        simpa only [add_sub_cancel_right, ← he] using h.2
      · apply List.Sublist.cons
        apply ih (lo + 1) (x :: xs)
        simp only [add_sub_cancel_right]
        change lo < x ∧ within x ((lo + 1) + n) xs
        exact ⟨by omega, he ▸ h.2⟩

theorem interior_iff_sublist (total : ℕ) (ht : 0 < total) (cuts : List ℤ) :
    within 0 total cuts ↔ cuts.Sublist (IntegerRange.interval 1 (total - 1)) := by
  have he : (1 : ℤ) + (total - 1 : ℕ) = total := by omega
  constructor
  · intro h
    apply sublist_interval_of_within
    simpa [he] using h
  · intro h
    have hw := within_sublist h (interval_within 1 (total - 1))
    simpa [he] using hw

/-- Enumerate every positive composition once by its increasing interior cuts. -/
def enumeration (n total : ℕ) : List (List ℤ) :=
  ((IntegerRange.interval 1 (total - 1)).sublistsLen (n - 1)).map (gaps total 0)

theorem enumeration_nodup (n total : ℕ) : (enumeration n total).Nodup :=
  List.Nodup.map (gaps_injective total 0) (List.nodup_sublistsLen _
    (within_nodup _ _ _ (interval_within 1 (total - 1))))

@[simp] theorem enumeration_length (n total : ℕ) :
    (enumeration n total).length = (total - 1).choose (n - 1) := by
  simp [enumeration, interval_length]

/-- The cut enumeration is exactly all positive ordered `n`-part compositions. -/
theorem mem_enumeration (n total : ℕ) (hn : 0 < n) (ht : n ≤ total) (parts : List ℤ) :
    parts ∈ enumeration n total ↔ positive n total parts := by
  have ht0 : 0 < total := lt_of_lt_of_le hn ht
  constructor
  · intro h
    obtain ⟨cuts, hc, rfl⟩ := List.mem_map.mp h
    obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp hc
    refine ⟨?_, (gaps_positive _ _ _).mpr ((interior_iff_sublist total ht0 cuts).mpr hsub), ?_⟩
    · rw [gaps_length, hlen]
      omega
    · simp
  · rintro ⟨hlen, hp, hs⟩
    have hne : parts ≠ [] := by intro he; subst parts; simp at hlen; omega
    apply List.mem_map.mpr
    refine ⟨cutPoints 0 parts, List.mem_sublistsLen.mpr ⟨?_, ?_⟩, ?_⟩
    · apply (interior_iff_sublist total ht0 _).mp
      apply cutPoints_within _ _ parts hne hp
      simpa using hs
    · simp [hlen]
    · apply gaps_cutPoints _ _ parts hne
      simpa using hs

end

end SampLib.Compositions
