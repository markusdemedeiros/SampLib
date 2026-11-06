module

public import SampLib.Distributions.Fenwick

@[expose] public section

/-! # The binary-lifting invariant

The selected cumulative interval stays in the current dyadic search window.
The remaining rank is measured relative to the accepted prefix.
-/

namespace FenwickMath

def Progress (step index selected : ℕ) : Prop :=
  (step = 0 ∧ index = selected) ∨
    (∃ a, step = 2 ^ a) ∧ index % (2 * step) = 0 ∧ selected < index + 2 * step

structure SearchInvariant {n : ℕ} (w : Fin n → ℕ) (target selected step index remaining : ℕ) :
    Prop where
  mass : prefixSum w index + remaining = target
  lower : index ≤ selected
  progress : Progress step index selected

theorem SearchInvariant.active {n : ℕ} {w : Fin n → ℕ}
    {target selected step index remaining : ℕ}
    (h : SearchInvariant w target selected step index remaining) (hs : 0 < step) :
    (∃ a, step = 2 ^ a) ∧ index % (2 * step) = 0 ∧ selected < index + 2 * step := by
  rcases h.progress with ⟨hz, _⟩ | hp
  · omega
  · exact hp

theorem SearchInvariant.at_zero {n : ℕ} {w : Fin n → ℕ}
    {target selected index remaining : ℕ}
    (h : SearchInvariant w target selected 0 index remaining) : index = selected := by
  rcases h.progress with ⟨_, heq⟩ | ⟨⟨a, ha⟩, _, _⟩
  · exact heq
  · have hp : 0 < 2 ^ a := by positivity
    omega

/-- The chosen half-window is either finished or aligned to its next dyadic step. -/
theorem progress_half {step index selected nextIndex : ℕ} (hp : ∃ a, step = 2 ^ a)
    (ha : index % (2 * step) = 0) (hnext : nextIndex = index ∨ nextIndex = index + step)
    (hlo : nextIndex ≤ selected) (hhi : selected < nextIndex + step) :
    Progress (step / 2) nextIndex selected := by
  rcases power_half_cases hp with hunit | ⟨hpower, hdouble⟩
  · left
    exact ⟨by simp [hunit], by omega⟩
  · right
    rcases aligned_half ha hdouble with ⟨hleft, hright⟩
    refine ⟨hpower, ?_, by omega⟩
    rcases hnext with rfl | rfl
    · exact hleft
    · exact hright

theorem SearchInvariant.initial {n : ℕ} (w : Fin n → ℕ) {target selected step : ℕ}
    (hq : Selects w target selected) (hp : ∃ a, step = 2 ^ a) (hn : n ≤ step) :
    SearchInvariant w target selected step 0 target := by
  refine ⟨by simp, Nat.zero_le _, Or.inr ⟨hp, by simp, ?_⟩⟩
  have hpos : 0 < step := by obtain ⟨a, rfl⟩ := hp; positivity
  have := hq.1
  omega

theorem SearchInvariant.skip {n : ℕ} {w : Fin n → ℕ}
    {target selected step index remaining : ℕ}
    (h : SearchInvariant w target selected step index remaining)
    (hq : Selects w target selected) (hs : 0 < step) (hnext : n < index + step) :
    SearchInvariant w target selected (step / 2) index remaining := by
  rcases h.active hs with ⟨hp, ha, _⟩
  refine ⟨h.mass, h.lower, progress_half hp ha (Or.inl rfl) h.lower ?_⟩
  have := hq.1
  omega

theorem SearchInvariant.advance {n : ℕ} {w : Fin n → ℕ}
    {target selected step index remaining : ℕ}
    (h : SearchInvariant w target selected step index remaining)
    (hq : Selects w target selected) (hs : 0 < step)
    (hm : cell w (index + step) ≤ remaining) :
    SearchInvariant w target selected (step / 2) (index + step)
      (remaining - cell w (index + step)) := by
  rcases h.active hs with ⟨hp, ha, hupper⟩
  have hbit := lowBit_aligned_of_power hp ha
  have hlo := next_le_selected w hq h.mass hbit hm
  exact ⟨remaining_after_advance w h.mass hbit hm, hlo,
    progress_half hp ha (Or.inr rfl) hlo (by omega)⟩

theorem SearchInvariant.stay {n : ℕ} {w : Fin n → ℕ}
    {target selected step index remaining : ℕ}
    (h : SearchInvariant w target selected step index remaining)
    (hq : Selects w target selected) (hs : 0 < step)
    (hm : remaining < cell w (index + step)) :
    SearchInvariant w target selected (step / 2) index remaining := by
  rcases h.active hs with ⟨hp, ha, _⟩
  have hbit := lowBit_aligned_of_power hp ha
  exact ⟨h.mass, h.lower,
    progress_half hp ha (Or.inl rfl) h.lower (selected_lt_next w hq h.mass hbit hm)⟩

end FenwickMath
