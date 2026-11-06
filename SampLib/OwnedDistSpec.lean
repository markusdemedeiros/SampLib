import SampLib.Samplers.SampleWithReplacement

/-! # Distribution specifications that preserve private sampler resources -/

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

/-- Exchange expected credit for output credit while retaining the sampler's state. -/
structure IsOwnedDistSpec (E : CoPset) (P : IProp GF) (e : Exp rT)
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (encode : α → Val rT) : Prop where
  spec (F : α → ℝ≥0∞) (hF : Measurable F) :
    iprop(P ∗ ↯ (∫⁻ x, F x ∂μ)) ⊢
      tglWp E e (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ P ∗ ↯ (F x)))

namespace IsOwnedDistSpec

variable {E : CoPset} {P : IProp GF} {e : Exp rT} {μ : MeasureTheory.Measure α}
  [MeasureTheory.IsProbabilityMeasure μ] {encode : α → Val rT}

/-- The continuation receives the private state together with the sampled credit. -/
theorem wp (h : IsOwnedDistSpec E P e μ encode) (F : α → ℝ≥0∞) (hF : Measurable F)
    (Φ : Val rT → IProp GF) :
    ⊢ P -∗ ↯ (∫⁻ x, F x ∂μ) -∗
      (∀ x : α, P -∗ ↯ (F x) -∗ Φ (encode x)) -∗ tglWp E e Φ := by
  iintro Hstate Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply h.spec F hF
    iframe Hstate Hcredit
  iintro %v ⟨%x, %hx, Hstate, Hcredit⟩
  subst v
  iapply Hcont $$ %x Hstate Hcredit

end IsOwnedDistSpec

section repetition

variable [Countable α] [MeasurableSingletonClass α]

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] [MeasurableSpace α]
  [Countable α] [MeasurableSingletonClass α] in
private theorem encode_cons (encode : α → Val rT) {n : ℕ} (x : α) (ys : Fin n → α) :
    pl(inr(({(encode x).fst}, {Exp.ofVal (listVal encode (List.ofFn ys))}))) =
      Exp.ofVal (listVal encode (List.ofFn (Fin.cons x ys))) := by
  simp [Exp.ofVal, List.ofFn_succ, listVal]

/-- Repeated reads of private sampler state still produce independent outputs. -/
theorem twp_repeatSample_owned (E : CoPset) (P : IProp GF) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (encode : α → Val rT) (sample : Val rT)
    (hsample : IsOwnedDistSpec E P pl(&sample.fst #()) μ encode) (n : ℕ)
    (F : (Fin n → α) → ℝ≥0∞) :
    ⊢ P -∗ ↯ (∫⁻ ys, F ys ∂SampleWithReplacement.law μ n) -∗
      tglWp E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ ys : Fin n → α,
          ⌜v = listVal encode (List.ofFn ys)⌝ ∗ P ∗ ↯ (F ys))) := by
  induction n with
  | zero =>
    iintro Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    iexists Fin.elim0
    isimp only [SampleWithReplacement.law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hstate Hcredit
    ipureintro
    simp [List.ofFn_zero, listVal]
  | succ n IH =>
    iintro Hstate Hcredit
    twp_pures
    twp_bind pl(&sample.fst #())
    isimp only [SampleWithReplacement.lintegral_law_succ μ n F (measurable_of_countable _)]
      at Hcredit
    iapply (hsample.wp
      (fun x => ∫⁻ ys, F (Fin.cons x ys) ∂SampleWithReplacement.law μ n)
      (measurable_of_countable _) _) $$ Hstate Hcredit
    iintro %x Hstate Hcredit
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply (IH (fun ys => F (Fin.cons x ys))) $$ Hstate Hcredit
    iintro %v ⟨%ys, %hv, Hstate, Hcredit⟩
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal encode (List.ofFn (Fin.cons x ys))))
    iexists Fin.cons x ys
    iframe Hstate Hcredit
    itrivial

/-- Resource-preserving independent repetition, ready for further composition. -/
theorem repeatSample_ownedDistSpec (E : CoPset) (P : IProp GF)
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsProbabilityMeasure μ]
    (encode : α → Val rT) (sample : Val rT)
    (hsample : IsOwnedDistSpec E P pl(&sample.fst #()) μ encode) (n : ℕ) :
    IsOwnedDistSpec E P pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
      (SampleWithReplacement.law μ n) (fun ys => listVal encode (List.ofFn ys)) where
  spec F _ := by
    iintro ⟨Hstate, Hcredit⟩
    iapply (twp_repeatSample_owned E P μ encode sample hsample n F) $$ Hstate Hcredit

end repetition

end

end SampLib
