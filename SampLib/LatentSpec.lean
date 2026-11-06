import SampLib.Templates
import SampLib.Distributions.LatentReal.Interval

/-! # Compositional specifications for deferred real draws

An oracle's heap state determines a posterior on a joint latent space. Reading
refines that posterior and supplies a shrinking rational enclosure, rather than
sampling a new independent real. Credits may depend on the entire latent state,
so aliases and shared arithmetic operands retain their dependence.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

/-- Mathematical state of a progressively observed joint latent draw. -/
structure Model (Ω S : Type) [MeasurableSpace Ω] where
  posterior : S → Measure Ω
  probability : ∀ s, IsProbabilityMeasure (posterior s)
  value : Ω → ℝ
  measurable_value : Measurable value
  refines : S → S → Prop
  refines_refl : ∀ s, refines s s
  refines_trans : ∀ {s t u}, refines s t → refines t u → refines s u
  absolutelyContinuous : ∀ {s t}, refines s t →
    Measure.AbsolutelyContinuous (posterior t) (posterior s)
  error : ℕ → Ω → ℝ
  error_tendsto : ∀ s, ∀ᵐ x ∂posterior s,
    Filter.Tendsto (fun n => error n x) Filter.atTop (nhds 0)

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

instance (D : Model Ω S) (s : S) : IsProbabilityMeasure (D.posterior s) := D.probability s

/-- The real-valued output law represented by a latent state. -/
def law (D : Model Ω S) (s : S) : Measure ℝ := (D.posterior s).map D.value

instance (D : Model Ω S) (s : S) : IsProbabilityMeasure (D.law s) :=
  inferInstanceAs (IsProbabilityMeasure ((D.posterior s).map D.value))

/-- The returned interval encloses the same latent value with vanishing error. -/
def Encloses (D : Model Ω S) (s : S) (n : ℕ) (I : RationalInterval) : Prop :=
  ∀ᵐ x ∂D.posterior s,
    I.Contains (D.value x) ∧ I.upperReal - I.lowerReal ≤ D.error n x

/-- Later reads preserve every earlier almost-everywhere enclosure. -/
theorem encloses_refines (D : Model Ω S) {s t : S} (h : D.refines s t)
    {n : ℕ} {I : RationalInterval} (hI : D.Encloses s n I) : D.Encloses t n I :=
  (D.absolutelyContinuous h).ae_le hI

end Model

/-- Object-language rational-interval representation. -/
def intervalVal {rT : Type} (I : RationalInterval) : Val rT :=
  .pair (.int I.lower) (.pair (.int I.upper) (.int I.denominator))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Observations retain the oracle and transfer arbitrary joint posterior credit. -/
structure IsOracleSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) : Prop where
  observe (v : Val rT) (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns v s ∗ ↯ (∫⁻ x, F x ∂D.posterior s)) ⊢
      tglWp E pl(&v.fst #int (n : ℤ))
        (fun result : Val rT => iprop(∃ (t : S) (I : RationalInterval),
          ⌜result = intervalVal I ∧ D.refines s t ∧ D.Encloses t n I⌝ ∗
          owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t)))

/-- Construction and all finite observations specify one deferred real draw. -/
structure IsLatentDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S) (initial : S)
    (owns : Val rT → S → IProp GF) : Prop where
  oracle : IsOracleSpec E D owns
  spec (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (∫⁻ x, F x ∂D.posterior initial)) ⊢
      tglWp E e (fun v : Val rT => iprop(∃ t : S,
        ⌜D.refines initial t⌝ ∗ owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t)))

namespace IsOracleSpec

/-- Observe through an alias while retaining all unrelated caller resources. -/
theorem wp {E : CoPset} {D : Model Ω S} {owns : Val rT → S → IProp GF}
    (h : IsOracleSpec E D owns) (v : Val rT) (s : S) (n : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ owns v s -∗ ↯ (∫⁻ x, F x ∂D.posterior s) -∗
      (∀ (t : S) (I : RationalInterval), ⌜D.refines s t ∧ D.Encloses t n I⌝ -∗
        owns v t -∗ ↯ (∫⁻ x, F x ∂D.posterior t) -∗ Φ (intervalVal I)) -∗
      tglWp E pl(&v.fst #int (n : ℤ)) Φ := by
  iintro Hstate Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply h.observe v s n F hF
    iframe Hstate Hcredit
  iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
  rcases hI with ⟨rfl, hrefines, hencloses⟩
  iapply Hcont $$ %t %I %⟨hrefines, hencloses⟩ Hstate Hcredit

end IsOracleSpec

namespace IsLatentDistSpec

/-- Build a lazy draw and pass its whole posterior state to a caller. -/
theorem wp {E : CoPset} {e : Exp rT} {D : Model Ω S} {initial : S}
    {owns : Val rT → S → IProp GF} (h : IsLatentDistSpec E e D initial owns)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂D.posterior initial) -∗
      (∀ (v : Val rT) (t : S), ⌜D.refines initial t⌝ -∗ owns v t -∗
        ↯ (∫⁻ x, F x ∂D.posterior t) -∗ Φ v) -∗ tglWp E e Φ := by
  iintro Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply h.spec F hF $$ Hcredit
  iintro %v ⟨%t, %ht, Hstate, Hcredit⟩
  iapply Hcont $$ %v %t %ht Hstate Hcredit

end IsLatentDistSpec

end specification

end

end SampLib.LatentReal
