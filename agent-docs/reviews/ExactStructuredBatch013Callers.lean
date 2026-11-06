import SampLib.Weighted.RecycledSamples

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured013

noncomputable section

open SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
theorem owned_frame {α : Type} [MeasurableSpace α] {E : CoPset} {P : IProp GF} {e : Exp rT}
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    {encode : α → Val rT} (h : IsOwnedDistSpec E P e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ P ∗ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ P ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨HP, Hcredit, HR⟩
  iapply (h.wp F hF _) $$ HP Hcredit
  iintro %x HP Hcredit
  iexists x
  iframe HP Hcredit HR
  itrivial

omit [ProbLangDist.IsUniformInt rT] in
theorem plain_frame {α : Type} [MeasurableSpace α] {E : CoPset} {e : Exp rT}
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial

-- One owned draw from the reset pool: n = 1 (no fresh bits), a power of two, a non-power.
example (E : CoPset) (pool : Loc) (R : IProp GF) :=
  owned_frame (RecycledUniform.recycledUniform_ownedDistSpec (GF := GF) (rT := rT) E pool 1)
    (fun _ => ∞) (measurable_of_countable _) R
example (E : CoPset) (pool : Loc) (R : IProp GF) :=
  owned_frame (RecycledUniform.recycledUniform_ownedDistSpec (GF := GF) (rT := rT) E pool 8)
    (fun _ => ∞) (measurable_of_countable _) R
example (E : CoPset) (pool : Loc) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (RecycledUniform.recycledUniform_ownedDistSpec (GF := GF) (rT := rT) E pool 7)
    F (measurable_of_countable _) R

private def draw (pool : Loc) (n : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.Weighted.recycledUniform #loc pool #int (n : ℤ)), .lam (by is_lc), by is_lc⟩

private instance uniform_closed : ClosedExp (Occil.Weighted.recycledUniform : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.Weighted.recycledUniform, Exp.fv]

private theorem draw_spec (E : CoPset) (pool : Loc) (n : ℕ) [NeZero n] :
    IsOwnedDistSpec (GF := GF) E (appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1))
      pl(&(draw (rT := rT) pool n).fst #()) (UniformInt.law n)
      (fun r : ℕ => Val.int (r : ℤ)) where
  spec F hF := by
    iintro Hinput
    twp_pure
    simp only [ClosedExp.openRec]
    iapply (RecycledUniform.recycledUniform_ownedDistSpec E pool n).spec F hF $$ Hinput

/-- Reusing one reset pool for repeated draws gives the IID joint law and keeps the pool. -/
example (E : CoPset) (pool : Loc) (n count : ℕ) [NeZero n]
    (F : (Fin count → ℕ) → ℝ≥0∞) (R : IProp GF) :=
  owned_frame (repeatSample_ownedDistSpec (GF := GF) E
    (appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1)) (UniformInt.law n)
    (fun r : ℕ => Val.int (r : ℤ)) (draw pool n) (draw_spec E pool n) count)
    F (measurable_of_countable _) R

/-- The stronger joint kernel also covers an arbitrary valid non-reset pool. -/
example (E : CoPset) (pool : Loc) (F : EntropyPool.JointResult → ℝ≥0∞) :=
  RecycledUniform.twp_recycledUniform (GF := GF) (rT := rT) E pool 3 5 6
    (by decide) (by decide) F

-- recycledSamples: count 0, count 1 with n = 1, and a larger count, with infinite credit.
example (E : CoPset) (R : IProp GF) :=
  plain_frame (RecycledSamples.recycledSamples_distSpec (GF := GF) (rT := rT) E 5 0)
    (fun _ => ∞) (measurable_of_countable _) R
example (E : CoPset) (R : IProp GF) :=
  plain_frame (RecycledSamples.recycledSamples_distSpec (GF := GF) (rT := rT) E 1 1)
    (fun _ => ∞) (measurable_of_countable _) R
example (E : CoPset) (F : List ℕ → ℝ≥0∞) (R : IProp GF) :=
  plain_frame (RecycledSamples.recycledSamples_distSpec (GF := GF) (rT := rT) E 6 4)
    F (measurable_of_countable _) R

-- A zero count with a nonpositive bound returns the empty list without failing.
example (E : CoPset) (R : IProp GF) :=
  plain_frame (RecycledSamples.recycledSamples_zero_distSpec (GF := GF) (rT := rT) E (-3))
    (fun _ => ∞) (measurable_of_countable _) R
example (E : CoPset) (R : IProp GF) :=
  plain_frame (RecycledSamples.recycledSamples_zero_distSpec (GF := GF) (rT := rT) E 0)
    (fun _ => ∞) (measurable_of_countable _) R

end

open SampLib MeasureTheory

-- The law is the list of IID uniform draws in sampling order.
example (n count : ℕ) :
    RecycledSamples.law n count =
      (SampleWithReplacement.law (UniformInt.law n) count).map List.ofFn := rfl

#print axioms SampLib.RecycledUniform.recycledUniform_ownedDistSpec
#print axioms SampLib.RecycledUniform.twp_recycledUniform
#print axioms SampLib.RecycledSamples.recycledSamples_distSpec
#print axioms SampLib.RecycledSamples.recycledSamples_zero_distSpec
#print axioms draw_spec

end ReviewExactStructured013
