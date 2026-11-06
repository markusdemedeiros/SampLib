import SampLib.AbsorbingChain

/-! # Finite-horizon CTE for an owned, progressively refined state

A uniform bound on retry probability funds the unresolved horizon. Every round
retains the physical state; the continuation credit may depend on its posterior.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.StatefulAbsorbingChain

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {S : Type}
local bi (IProp GF)

/-- A finite unfolding spends one unit only at the unresolved horizon. -/
theorem twp_finite (E : CoPset) (e : ℕ → Exp rT) (owns : S → IProp GF)
    (post : S → Val rT → IProp GF) (credit : ℕ → S → ℝ≥0∞) (q : ℕ → ℝ≥0∞)
    (step : ∀ n c,
      (∀ s, ⊢ owns s -∗ ↯ (credit (n + 1) s + c) -∗ tglWp E (e (n + 1)) (post s)) →
      ∀ s, ⊢ owns s -∗ ↯ (credit n s + q n * c) -∗ tglWp E (e n) (post s))
    (start depth : ℕ) :
    ∀ s, ⊢ owns s -∗ ↯ (credit start s + AbsorbingChain.survival q start depth) -∗
      tglWp E (e start) (post s) := by
  induction depth generalizing start with
  | zero =>
    intro s
    iintro Hstate Hcredit
    iexfalso
    iapply ErrorCredit.contradict (by simp) $$ Hcredit
  | succ depth ih =>
    simpa only [AbsorbingChain.survival_succ] using
      step start (AbsorbingChain.survival q (start + 1) depth) (ih (start + 1))

/-- Vanishing uniform survival removes every auxiliary termination credit. -/
theorem twp_of_survival (E : CoPset) (e : ℕ → Exp rT) (owns : S → IProp GF)
    (post : S → Val rT → IProp GF) (credit : ℕ → S → ℝ≥0∞) (q : ℕ → ℝ≥0∞)
    (step : ∀ n c,
      (∀ s, ⊢ owns s -∗ ↯ (credit (n + 1) s + c) -∗ tglWp E (e (n + 1)) (post s)) →
      ∀ s, ⊢ owns s -∗ ↯ (credit n s + q n * c) -∗ tglWp E (e n) (post s))
    (start : ℕ) (nonvalue : (e start).toVal? = none)
    (absorbs : Filter.Tendsto (AbsorbingChain.survival q start) Filter.atTop (nhds 0)) :
    ∀ s, ⊢ owns s -∗ ↯ (credit start s) -∗ tglWp E (e start) (post s) := by
  intro s
  have hlimit : Filter.liminf (fun depth => credit start s + AbsorbingChain.survival q start depth)
      Filter.atTop = credit start s := by
    simpa using (tendsto_const_nhds.add absorbs).liminf_eq
  iintro Hstate Hcredit
  iapply (twp_err_liminf (l := Filter.atTop) (S := Set.univ)
    (ε := fun depth : ℕ => credit start s + AbsorbingChain.survival q start depth)
    Filter.univ_mem nonvalue)
  isplitl [Hcredit]
  · isimp only [hlimit]
    iexact Hcredit
  · iintro %depth - Hcredit
    iapply twp_finite E e owns post credit q step start depth s $$ Hstate Hcredit

end

end SampLib.StatefulAbsorbingChain
