import SampLib.Latent.LatentPayloadSpec
import SampLib.Latent.LatentViews
import SampLib.PSRN.Laws.IntervalSchedules

/-! # Deterministic interval representations of a shared latent world

The enclosure protocol alone does not bound coarse reciprocal intervals. This
extension records the actual interval determined by the latent world and the
requested precision, preserving aliases and the existing posterior semantics.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

/-- All finite observations represent one measurable, convergent interval sequence. -/
structure Representation {Ω S : Type} [MeasurableSpace Ω] (D : Model Ω S) where
  interval : ℕ → Ω → RationalInterval
  measurable_lower : ∀ n, Measurable (fun x => (interval n x).lower)
  measurable_upper : ∀ n, Measurable (fun x => (interval n x).upper)
  measurable_denominator : ∀ n, Measurable (fun x => (interval n x).denominator)
  approximates : ∀ s, ∀ᵐ x ∂D.posterior s,
    RationalInterval.Approximates (fun n => interval n x) (D.value x)

namespace Representation

variable {Ω S : Type} [MeasurableSpace Ω] {D : Model Ω S}

/-- An observation identifies the interval at every compatible latent world. -/
def Observed (R : Representation D) (s : S) (n : ℕ) (I : RationalInterval) : Prop :=
  ∀ᵐ x ∂D.posterior s, I = R.interval n x

theorem observed_refines (R : Representation D) {s t : S} (h : D.refines s t)
    {n : ℕ} {I : RationalInterval} (hI : R.Observed s n I) : R.Observed t n I :=
  (D.absolutelyContinuous h).ae_le hI

end Representation

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Reads retain full joint credit and identify their actual deterministic interval. -/
structure IsRepresentedOracleSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (owns : Val rT → S → IProp GF) : Prop where
  observe (v : Val rT) (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns v s ∗ ↯ (∫⁻ x, F x ∂D.posterior s)) ⊢
      tglWp E pl(&v.fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ (t : S) (I : RationalInterval),
          ⌜result = intervalVal I ∧ D.refines s t ∧ D.Encloses t n I ∧ R.Observed t n I⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t)))

namespace IsRepresentedOracleSpec

theorem forget {E : CoPset} {D : Model Ω S} {R : Representation D}
    {owns : Val rT → S → IProp GF} (h : IsRepresentedOracleSpec E D R owns) :
    IsOracleSpec E D owns where
  observe v s n F hF := by
    iintro Hstate
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply h.observe v s n F hF $$ Hstate
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    iexists t, I
    iframe Hstate Hcredit
    ipureintro
    exact ⟨hI.1, hI.2.1, hI.2.2.1⟩

/-- A caller keeps every unrelated resource while observing the represented real. -/
theorem wp {E : CoPset} {D : Model Ω S} {R : Representation D}
    {owns : Val rT → S → IProp GF} (h : IsRepresentedOracleSpec E D R owns)
    (v : Val rT) (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (Φ : Val rT → IProp GF) :
    ⊢ owns v s -∗ ↯ (∫⁻ x, F x ∂D.posterior s) -∗
      (∀ (t : S) (I : RationalInterval),
        ⌜D.refines s t ∧ D.Encloses t n I ∧ R.Observed t n I⌝ -∗
        owns v t -∗ ↯ (∫⁻ x, F x ∂D.posterior t) -∗ Φ (intervalVal I)) -∗
      tglWp E pl(&v.fst #int (n : ℤ)) Φ := by
  iintro Hstate Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply h.observe v s n F hF
    iframe Hstate Hcredit
  iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
  rcases hI with ⟨rfl, hI⟩
  iapply Hcont $$ %t %I %hI Hstate Hcredit

end IsRepresentedOracleSpec

/-- A fixed handle observes the same one owned physical world at every call. -/
abbrev IsRepresentedViewSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (handle : Val rT) :=
  IsRepresentedOracleSpec E D R (ViewOwns handle P)

/-- The represented constructor and all observations describe the actual program. -/
structure IsRepresentedDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S)
    (R : Representation D) (initial : S) (owns : Val rT → S → IProp GF)
    extends IsLatentPayloadSpec E e D initial owns where
  oracle : IsRepresentedOracleSpec E D R owns

theorem IsRepresentedDistSpec.forget {E : CoPset} {e : Exp rT} {D : Model Ω S}
    {R : Representation D} {initial : S} {owns : Val rT → S → IProp GF}
    (h : IsRepresentedDistSpec E e D R initial owns) :
    IsLatentDistSpec E e D initial owns := ⟨h.oracle.forget, h.spec⟩

end specification

end

end SampLib.LatentReal
