import SampLib.Basic
import Metrology.Iris.LocalBI

/-!
# Compositional CTE distribution specifications

`IsDistSpec E e μ encode` specifies a sampler using arbitrary measurable
continuation credits on its mathematical output type. Its expectation is taken
under the probability measure `μ`; the program returns `encode x` with the
continuation credit `F x`.

The specification is relative to the current ghost state and mask, so it can be
used inside another CTE proof. The mathematical output type is retained in the
postcondition. Continuation credits may be unbounded, including infinity.

To verify a sampler, establish its measurable credit kernel and conservation
identity, then prove the `spec` field. To use a verified sampler under `twp_bind`,
apply `h.wp F hF _ $$ Hcredit`, where `h` is the sampler's distribution spec,
and supply the continuation for each mathematical output.
That continuation is an Iris assertion and can carry the caller's resources.

The encoder need not be measurable or injective for this program-logic rule.
Such conditions belong to a separate adequacy argument when one is required.
-/

open Iris Iris.BI Iris.ProofMode ProbLang ProbLang.TotalEris
  ProbLang.TotalEris.ErisWpGS
open scoped ENNReal

namespace SampLib

noncomputable section

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

/-- A typed CTE distribution specification, reusable in the current proof context.
Probability normalization is required; credit redistribution alone can also hold
for measures of mass greater than one, which would not identify an output law. -/
structure IsDistSpec (E : CoPset) (e : Exp rT) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (encode : α → Val rT) : Prop where
  /-- Exchange the expected continuation credit for the credit of the result. -/
  spec (F : α → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (∫⁻ x, F x ∂μ)) ⊢
      tglWp E e (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x)))

namespace IsDistSpec

variable {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ] {encode : α → Val rT}

/-- Use a distribution spec with a caller-supplied continuation. Its resources
remain available until the sampler returns its mathematical output. -/
theorem wp (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) -∗
      (∀ x : α, ↯ (F x) -∗ Φ (encode x)) -∗ tglWp E e Φ := by
  iintro Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply h.spec F hF $$ Hcredit
  iintro %v ⟨%x, %hx, Hcredit⟩
  subst v
  iapply Hcont $$ %x Hcredit

end IsDistSpec

end

end SampLib
