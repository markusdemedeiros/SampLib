import SampLib.PSRN.Support.LatentPiModel
import SampLib.PSRN.Support.LatentPiOwnership

/-! # Observing one component of an owned finite product

The selected oracle receives its conditional joint credit. Its refined resource
is then restored to the one owned vector, together with the updated full credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.PiModel

noncomputable section

section mathematics

open MeasureTheory

variable {n : ℕ} {Ω S : Fin n → Type} [∀ i, MeasurableSpace (Ω i)]

theorem posterior_update (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin n) (t : S i) :
    posterior Ds (Function.update s i t) =
      Measure.pi (Function.update (fun j => (Ds j).posterior (s j)) i ((Ds i).posterior t)) := by
  unfold posterior
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

theorem refines_update (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin n) (t : S i) (ht : (Ds i).refines (s i) t) :
    (world Ds).refines s (Function.update s i t) := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using ht
  · simpa only [Function.update_of_ne hj] using (Ds j).refines_refl (s j)

theorem encloses_update (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin n) {t : S i} {bits : ℕ} {I : RationalInterval} (hI : (Ds i).Encloses t bits I) :
    (view Ds i).Encloses (Function.update s i t) bits I := by
  have hI' : (Ds i).Encloses ((Function.update s i t) i) bits I := by simpa using hI
  exact
    (measurePreserving_eval
      (fun j => (Ds j).posterior ((Function.update s i t) j)) i).quasiMeasurePreserving.ae hI'

theorem observed_update (Ds : ∀ i, Model (Ω i) (S i)) (Rs : ∀ i, Representation (Ds i))
    (s : ∀ i, S i) (i : Fin n) {t : S i} {bits : ℕ} {I : RationalInterval}
    (hI : (Rs i).Observed t bits I) :
    (representation Ds Rs i).Observed (Function.update s i t) bits I := by
  have hI' : (Rs i).Observed ((Function.update s i t) i) bits I := by simpa using hI
  exact
    (measurePreserving_eval
      (fun j => (Ds j).posterior ((Function.update s i t) j)) i).quasiMeasurePreserving.ae hI'

end mathematics

section disintegration

open MeasureTheory

variable {n : ℕ} {Ω S : Fin (n + 1) → Type} [∀ i, MeasurableSpace (Ω i)]

def coordinateCredit (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin (n + 1)) (F : (∀ j, Ω j) → ℝ≥0∞) : Ω i → ℝ≥0∞ :=
  FiniteProductPosterior.coordinateCredit (fun j => (Ds j).posterior (s j)) i F

theorem measurable_coordinateCredit (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin (n + 1)) {F : (∀ j, Ω j) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (coordinateCredit Ds s i F) :=
  FiniteProductPosterior.measurable_coordinateCredit _ i hF

theorem expectation_coordinate (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin (n + 1)) (F : (∀ j, Ω j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂posterior Ds s =
      ∫⁻ x, coordinateCredit Ds s i F x ∂(Ds i).posterior (s i) :=
  FiniteProductPosterior.expectation_coordinate _ i F hF

theorem expectation_updated (Ds : ∀ i, Model (Ω i) (S i)) (s : ∀ i, S i)
    (i : Fin (n + 1)) (t : S i) (F : (∀ j, Ω j) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂posterior Ds (Function.update s i t) =
      ∫⁻ x, coordinateCredit Ds s i F x ∂(Ds i).posterior t := by
  rw [posterior_update]
  exact FiniteProductPosterior.expectation_update _ i _ F hF

end disintegration

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {n : ℕ} {Ω S : Fin n → Type} [∀ i, MeasurableSpace (Ω i)]
local bi (IProp GF)

/-- Every read returns the same owned vector and the selected exact interval certificate. -/
theorem represented_coordinateSpec (E : CoPset) (Ds : ∀ i, Model (Ω i) (S i))
    (Rs : ∀ i, Representation (Ds i)) (O : ∀ i, Val rT → S i → IProp GF)
    (handles : Fin n → Val rT) (i : Fin n)
    (hspec : IsRepresentedOracleSpec E (Ds i) (Rs i) (O i)) :
    IsRepresentedViewSpec E (view Ds i) (representation Ds Rs i)
      (owns S O handles) (handles i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine ⟨fun v s bits F hF => ?_⟩
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    ihave ⟨Hcomponent, Hrestore⟩ := access S O handles s i $$ Hstate
    isimp only [view, world, expectation_coordinate Ds s i F hF] at Hcredit
    iapply (IsRepresentedOracleSpec.wp hspec (handles i) (s i) bits
      (coordinateCredit Ds s i F) (measurable_coordinateCredit Ds s i hF) _)
      $$ Hcomponent Hcredit
    iintro %t %I %hI Hcomponent Hcredit
    isimp only [← expectation_updated Ds s i t F hF] at Hcredit
    ihave Hstate := Hrestore $$ %t Hcomponent
    iexists Function.update s i t, I
    isplitl []
    · ipureintro
      exact ⟨rfl, refines_update Ds s i t hI.1, encloses_update Ds s i hI.2.1,
        observed_update Ds Rs s i hI.2.2⟩
    isimp only [ViewOwns, view, world]
    iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.PiModel
