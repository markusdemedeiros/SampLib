import SampLib.Bernoulli.Support.EnvelopeRealization

/-! # Deterministic callback contracts for visited envelope rows -/

open ProbLang

namespace SampLib.EnvelopeFactory

open FactoryFractions

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

abbrev BoundsSpec (E : CoPset) (a : Coefficients) (r : a.Realization)
    (bounds : Val rT) : Prop :=
  ∀ t, 0 < t → ∀ k : Fin (a.degree t + 1),
    ⊢ tglWp E pl(&bounds.fst #int (a.degree t : ℤ) #int ((k : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = r.encode t k⌝))

abbrev NextSpec (E : CoPset) (a : Coefficients) (next : Val rT) : Prop :=
  ∀ t, ⊢ tglWp E pl(&next.fst #int (a.degree t : ℤ))
    (fun v : Val rT => iprop(⌜v = Val.int (a.degree (t + 1) : ℤ)⌝))

/-- The conditional source loop visits only valid entries of one positive previous row. -/
theorem bounds_row (E : CoPset) (a : Coefficients) (r : a.Realization) (bounds : Val rT)
    (hbounds : BoundsSpec (GF := GF) E a r bounds) (t : ℕ) :
    0 < a.degree t → ∀ j : ℕ, j ≤ a.degree t →
      ⊢ tglWp E pl(&bounds.fst #int (a.degree t : ℤ) #int (j : ℤ))
        (fun v : Val rT => iprop(⌜v =
          Val.pair (r.row t j false).encode (r.row t j true).encode⌝)) := by
  intro hn j hj
  have ht : 0 < t := Nat.pos_of_ne_zero ((a.degree_eq_zero t).not.mp hn.ne')
  have h := hbounds t ht ⟨j, Nat.lt_succ_iff.mpr hj⟩
  simpa only [Coefficients.Realization.encode, Coefficients.Realization.row,
    dite_eq_left (Nat.lt_succ_iff.mpr hj)] using h

/-- The actual conditional closure computes the exact elevated lower or upper coefficient. -/
theorem twp_conditional (E : CoPset) (a : Coefficients) (r : a.Realization)
    (bounds : Val rT) (hbounds : BoundsSpec (GF := GF) E a r bounds)
    (t : ℕ) (k : Fin (a.degree (t + 1) + 1)) (high : Bool) :
    ⊢ tglWp E pl(&(EnvelopeConditionalAverage.conditionalClosure bounds
      (a.degree t) (a.degree (t + 1)) k).fst &(Val.bool high).fst)
      (fun v : Val rT => iprop(⌜v = encode
        (if high then a.upperBarQ t k else a.lowerBarQ t k)⌝)) := by
  have h := EnvelopeConditionalAverage.twp_conditionalClosure (rT := rT) (GF := GF)
    E (r.row t) bounds (a.degree t) (a.degree (t + 1)) k high (a.grows t).le
    (Nat.le_of_lt_succ k.isLt) (bounds_row E a r bounds hbounds t)
  simpa only [r.conditionalMean_eq] using h

end specification

end

end SampLib.EnvelopeFactory
