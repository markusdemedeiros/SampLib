module

public import SampLib.PSRN.Laws.IntervalSchedules
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! # Measurable first precision separating an enclosure from zero

Search starts at the requested precision. When no enclosure separates, the
selector returns that request; nonzero convergent representations always separate.
-/

open Set MeasureTheory

namespace SampLib.LatentReal.ReciprocalSelection

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Ω : Type*}

/-- Integer endpoint signs suffice because interval denominators are positive. -/
def separated (I : RationalInterval) : Prop := 0 < I.lower ∨ I.upper < 0

/-- Totalize the search by admitting only `n` when no separating index exists. -/
def candidate (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω) (k : ℕ) : Prop :=
  (n ≤ k ∧ separated (I k ω)) ∨ (k = n ∧ ¬ ∃ j, n ≤ j ∧ separated (I j ω))

theorem exists_candidate (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω) :
    ∃ k, candidate I n ω k := by
  by_cases h : ∃ k, n ≤ k ∧ separated (I k ω)
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨n, Or.inr ⟨rfl, h⟩⟩

/-- Least separating precision at or above `n`, with fallback `n` if none exists. -/
def precision (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω) : ℕ :=
  Nat.find (exists_candidate I n ω)

theorem precision_ge (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω) :
    n ≤ precision I n ω := by
  rcases Nat.find_spec (exists_candidate I n ω) with h | h
  · exact h.1
  · exact h.1.symm.le

theorem precision_separated (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω)
    (h : ∃ k, n ≤ k ∧ separated (I k ω)) : separated (I (precision I n ω) ω) := by
  exact ((Nat.find_spec (exists_candidate I n ω)).resolve_right (fun hn => hn.2 h)).2

theorem precision_min (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω)
    {k : ℕ} (hk : n ≤ k) (hsep : separated (I k ω)) : precision I n ω ≤ k :=
  Nat.find_min' (exists_candidate I n ω) (Or.inl ⟨hk, hsep⟩)

theorem precision_spec (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω)
    (h : ∃ k, n ≤ k ∧ separated (I k ω)) :
    n ≤ precision I n ω ∧ separated (I (precision I n ω) ω) ∧
      ∀ k, n ≤ k → separated (I k ω) → precision I n ω ≤ k :=
  ⟨precision_ge I n ω, precision_separated I n ω h, fun _ => precision_min I n ω⟩

theorem precision_of_none (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω)
    (h : ¬ ∃ k, n ≤ k ∧ separated (I k ω)) : precision I n ω = n :=
  le_antisymm (Nat.find_min' (exists_candidate I n ω) (Or.inr ⟨rfl, h⟩))
    (precision_ge I n ω)

/-- Convergent enclosures of a nonzero value always reach a separating precision. -/
theorem precision_separated_of_approximates (I : ℕ → Ω → RationalInterval) (n : ℕ) (ω : Ω)
    {x : ℝ} (h : RationalInterval.Approximates (fun k => I k ω) x) (hx : x ≠ 0) :
    separated (I (precision I n ω) ω) := by
  apply precision_separated I n ω
  exact ((Filter.eventually_ge_atTop n).and (h.eventually_separated hx)).exists

variable [MeasurableSpace Ω]

/-- No denominator measurability is needed to decide zero separation. -/
theorem measurable_precision (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper)) (n : ℕ) :
    Measurable (precision I n) := by
  have hsep k : MeasurableSet {ω | separated (I k ω)} :=
    (measurableSet_lt measurable_const (hl k)).union
      (measurableSet_lt (hu k) measurable_const)
  have hgood k : MeasurableSet {ω | n ≤ k ∧ separated (I k ω)} :=
    (MeasurableSet.const (n ≤ k)).inter (hsep k)
  have hexists : MeasurableSet {ω | ∃ k, n ≤ k ∧ separated (I k ω)} := by
    simpa only [ofPred_exists] using MeasurableSet.iUnion hgood
  apply measurable_find (exists_candidate I n)
  intro k
  exact (hgood k).union ((MeasurableSet.const (k = n)).inter hexists.compl)

/-- Every measurable field remains measurable after the adaptive lookup. -/
theorem measurable_selected {β : Type*} [MeasurableSpace β]
    (I : ℕ → Ω → RationalInterval)
    (hl : ∀ k, Measurable (fun ω => (I k ω).lower))
    (hu : ∀ k, Measurable (fun ω => (I k ω).upper))
    (f : ℕ → Ω → β) (hf : ∀ k, Measurable (f k)) (n : ℕ) :
    Measurable (fun ω => f (precision I n ω) ω) := by
  have hfamily : Measurable (fun z : ℕ × Ω => f z.1 z.2) :=
    measurable_from_prod_countable_right hf
  exact hfamily.comp ((measurable_precision I hl hu n).prodMk measurable_id)

end

end SampLib.LatentReal.ReciprocalSelection
