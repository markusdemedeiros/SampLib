import SampLib.Weighted.Laws.RealCategoricalCell
import SampLib.Latent.Laws.Uniform
import SampLib.Latent.LatentDigitPrefix

/-! # Whole-cell tests for Han–Hoshi interval refinement -/

namespace SampLib.HanHoshi

/-- The current dyadic cell lies within one cumulative-weight interval. -/
def Fits (total value denominator before after : ℕ) : Prop :=
  before * denominator ≤ value * total ∧ (value + 1) * total ≤ after * denominator

instance (total value denominator before after : ℕ) :
    Decidable (Fits total value denominator before after) :=
  inferInstanceAs (Decidable (before * denominator ≤ value * total ∧
    (value + 1) * total ≤ after * denominator))

def scan (total value denominator : ℕ) : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | w :: ws, before =>
    if Fits total value denominator before (before + w) then some 0
    else (scan total value denominator ws (before + w)).map Nat.succ

/-- Every reported position certifies both ends of its complete cell. -/
theorem scan_some (total value denominator : ℕ) (ws : List ℕ) (before i : ℕ)
    (h : scan total value denominator ws before = some i) :
    i < ws.length ∧
      Fits total value denominator (before + (ws.take i).sum)
        (before + (ws.take (i + 1)).sum) := by
  induction ws generalizing before i with
  | nil => simp [scan] at h
  | cons w ws ih =>
    rw [scan] at h
    split_ifs at h with hf
    · have hi : i = 0 := by simpa using h.symm
      subst i
      exact ⟨by simp, by simpa only [List.take_zero, List.sum_nil, add_zero,
        List.take_succ_cons, List.sum_cons] using hf⟩
    · cases hr : scan total value denominator ws (before + w) with
      | none =>
        simp only [hr, Option.map_none] at h
        cases h
      | some j =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst i
        obtain ⟨hj, hfit⟩ := ih (before + w) j hr
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        simpa only [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using hfit

/-- Failure means no input interval contains the whole cell. -/
theorem scan_none (total value denominator : ℕ) (ws : List ℕ) (before : ℕ) :
    scan total value denominator ws before = none ↔
      ∀ i, i < ws.length →
        ¬Fits total value denominator (before + (ws.take i).sum)
          (before + (ws.take (i + 1)).sum) := by
  induction ws generalizing before with
  | nil => simp [scan]
  | cons w ws ih =>
    by_cases hf : Fits total value denominator before (before + w)
    · rw [scan, ite_eq_left hf]
      constructor
      · simp
      · intro h
        exact False.elim (h 0 (by simp) (by simpa using hf))
    · rw [scan, ite_eq_right hf, Option.map_eq_none_iff, ih]
      constructor
      · intro h i hi
        cases i with
        | zero => simpa using hf
        | succ i =>
          simpa only [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using
            h i (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)
      · intro h i hi
        simpa only [List.take_succ_cons, List.sum_cons, Nat.add_assoc] using
          h (i + 1) (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi)

end SampLib.HanHoshi
