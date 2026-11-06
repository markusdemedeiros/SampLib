import SampLib.Discrete.WalleniusMultivariate

/-! # Ordinary multicolor sampling without replacement -/

open ProbLang
open scoped ENNReal SampLib.UrnTerms

namespace SampLib.MultivariateHypergeometric

noncomputable section

@[pl_fold] private def ones {rT : Type _} : Exp rT := pl%
  rec build xs := case! xs
    | inl(u) => inl(#())
    | inr(p) => inr((#1, build (snd(p))))

private theorem cons_value {rT : Type _} [ProbLangℝ rT] (xs : List ℕ) :
    (pl(inr((#1, {Exp.ofVal (NatCounters.encode xs)}))) : Exp rT) =
      Exp.ofVal (NatCounters.encode (1 :: xs)) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_ones (E : CoPset) (pop : List ℕ) :
    ⊢ tglWp E pl(&ones &(NatCounters.encode pop).fst)
      (fun v : Val rT => iprop(⌜v = NatCounters.encode (List.replicate pop.length 1)⌝)) := by
  induction pop with
  | nil =>
    simp only [NatCounters.encode, listVal]
    twp_pures
    twp_value
    imodintro
    ipureintro
    rfl
  | cons x pop IH =>
    simp only [NatCounters.encode, listVal]
    iterate 5 twp_pure
    have hnext := IH
    simp [ones, Exp.close, Exp.closeRec] at hnext
    twp_bind_from hnext
    iapply tglWp_wand
    isplitl []
    · iapply hnext
    iintro %v %hv
    subst v
    rw [cons_value]
    iapply (tglWp_value (v := NatCounters.encode (1 :: List.replicate pop.length 1)))
    ipureintro
    simp [List.replicate_succ]

/-- Unit odds specialize the canonical Wallenius law to ordinary urn sampling. -/
theorem twp_multivariateHypergeometric (E : CoPset) (n : ℕ) (pop : List ℕ)
    (hn : n ≤ pop.sum) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂Wallenius.law n pop (List.replicate pop.length 1)) -∗
      tglWp E pl(&Occil.DiscreteExtra.multivariateHypergeometric #int (n : ℤ)
        &(NatCounters.encode pop).fst)
        (fun v : Val rT => iprop(∃ ys : List ℕ, ⌜v = NatCounters.encode ys⌝ ∗ ↯ (F ys))) := by
  have hones := twp_ones (rT := rT) (GF := GF) E pop
  simp [ones, Exp.close, Exp.closeRec] at hones
  iintro Hcredit
  isimp [Occil.DiscreteExtra.multivariateHypergeometric, Exp.close, Exp.closeRec,
    ClosedExp.openRec, ClosedExp.closeRec]
  iterate 3 twp_pure
  twp_bind_from hones
  iapply tglWp_wand
  isplitl []
  · iapply hones
  iintro %v %hv
  subst v
  simp only [ClosedExp.openRec, Exp.ofVal]
  iapply WalleniusMultivariate.twp_walleniusMultivariate E n pop (List.replicate pop.length 1)
    hn (by simp) (by simp) F $$ Hcredit

/-- The unit-odds word likelihood is the ordinary without-replacement urn law. -/
theorem multivariateHypergeometric_distSpec (E : CoPset) (n : ℕ) (pop : List ℕ)
    (hn : n ≤ pop.sum) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.multivariateHypergeometric #int (n : ℤ)
      &(NatCounters.encode pop).fst) (Wallenius.law n pop (List.replicate pop.length 1))
      NatCounters.encode where
  spec F _ := wand_entails (twp_multivariateHypergeometric E n pop hn F)

end specification

end

end SampLib.MultivariateHypergeometric
