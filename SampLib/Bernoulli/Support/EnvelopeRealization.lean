import SampLib.Bernoulli.Laws.EnvelopeRationalState
import SampLib.Bernoulli.Support.EnvelopeConditionalAverage

/-! # Raw callback fractions realizing the visited coefficient rows

Only positive visited degrees need a callback contract. The virtual initial row
is the source's explicit zero/one shortcut; its callback is never evaluated.
-/

open ProbLang Finset

namespace SampLib.EnvelopeFactory.Coefficients

noncomputable section

variable (a : Coefficients)

theorem degree_strictMono : StrictMono a.degree := strictMono_nat_of_lt_succ a.grows

theorem degree_eq_zero (t : ℕ) : a.degree t = 0 ↔ t = 0 := by
  constructor
  · intro h
    apply a.degree_strictMono.injective
    simpa only [a.initial_degree] using h
  · rintro rfl
    exact a.initial_degree

theorem degree_pos (t : ℕ) (ht : 0 < t) : 0 < a.degree t := by
  simpa only [a.initial_degree] using a.degree_strictMono ht

@[simp] theorem lowerBarQ_zero (k : Fin (a.degree 1 + 1)) : a.lowerBarQ 0 k = 0 := by
  simp [lowerBarQ, a.lower_initial]

@[simp] theorem upperBarQ_zero (k : Fin (a.degree 1 + 1)) : a.upperBarQ 0 k = 1 := by
  simp only [upperBarQ, a.upper_initial, mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    ReverseBinomial.coefficient (a.degree 0) (a.degree 1) k j)]
  exact ReverseBinomial.coefficient_sum_degree _ _ _ (a.grows 0).le
    (Nat.le_of_lt_succ k.isLt)

structure Realization where
  raw : (t : ℕ) → Fin (a.degree t + 1) → Bool → FactoryFractions.Fraction
  value : ∀ t, 0 < t → ∀ k high, (raw t k high).value =
    if high then a.upper t k else a.lower t k

namespace Realization

variable {a} (r : a.Realization)

def encode {rT : Type} (t : ℕ) (k : Fin (a.degree t + 1)) : Val rT :=
  Val.pair (r.raw t k false).encode (r.raw t k true).encode

/-- The finite previous row, extended only to state the generic source-loop contract. -/
def row (t j : ℕ) (high : Bool) : FactoryFractions.Fraction :=
  if h : j < a.degree t + 1 then r.raw t ⟨j, h⟩ high else .ofRat 0

@[simp] theorem row_fin (t : ℕ) (j : Fin (a.degree t + 1)) (high : Bool) :
    r.row t j high = r.raw t j high := by
  simp only [row, dite_eq_left j.isLt]

/-- The source's exact finite average is precisely the rational degree-elevated row. -/
theorem conditionalMean_eq (t : ℕ) (k : Fin (a.degree (t + 1) + 1)) (high : Bool) :
    EnvelopeConditionalAverage.mean (r.row t) (a.degree t) (a.degree (t + 1)) k high =
      if high then a.upperBarQ t k else a.lowerBarQ t k := by
  by_cases ht : t = 0
  · subst t
    simp only [EnvelopeConditionalAverage.mean, a.initial_degree, ite_true,
      a.upperBarQ_zero, a.lowerBarQ_zero]
  · have hd : a.degree t ≠ 0 := (a.degree_eq_zero t).not.mpr ht
    simp only [EnvelopeConditionalAverage.mean, ite_eq_right hd]
    rw [← Fin.sum_univ_eq_sum_range (fun j =>
      ReverseBinomial.coefficient (a.degree t) (a.degree (t + 1)) k j *
        (r.row t j high).value)]
    have hpos : 0 < t := Nat.pos_of_ne_zero ht
    cases high
    · simp only [Bool.false_eq_true, ite_false, lowerBarQ]
      apply sum_congr rfl
      intro j _
      rw [r.row_fin, r.value t hpos j false]
      rfl
    · simp only [ite_true, upperBarQ]
      apply sum_congr rfl
      intro j _
      rw [r.row_fin, r.value t hpos j true]
      rfl

end Realization

end

end SampLib.EnvelopeFactory.Coefficients
