import SampLib.Templates
import SampLib.Common.Laws.AbsorbingChain

/-! # CTE induction for an indexed absorbing chain

Finite unfolding leaves only the probability of surviving the chosen horizon.
Its vanishing limit proves total correctness without an expected-time bound.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AbsorbingChain

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A finite horizon pays the full expectation and the unresolved survival mass.
The one-step rule is ordinary symbolic execution, given its recursive continuation. -/
theorem twp_finite (E : CoPset) (e : ℕ → Exp rT) (Φ : Val rT → IProp GF)
    (q exit credit : ℕ → ℝ≥0∞)
    (conservation : ∀ n, credit n = exit n + q n * credit (n + 1))
    (step : ∀ n c, (⊢ ↯ c -∗ tglWp E (e (n + 1)) Φ) →
      ⊢ ↯ (exit n + q n * c) -∗ tglWp E (e n) Φ)
    (start depth : ℕ) :
    ⊢ ↯ (credit start + survival q start depth) -∗ tglWp E (e start) Φ := by
  induction depth generalizing start with
  | zero =>
    iintro Hcredit
    iexfalso
    iapply ErrorCredit.contradict (by simp) $$ Hcredit
  | succ depth ih =>
    have h := step start (credit (start + 1) + survival q (start + 1) depth)
      (ih (start + 1))
    have hbudget : exit start + q start *
        (credit (start + 1) + survival q (start + 1) depth) =
        credit start + survival q start (depth + 1) := by
      rw [conservation start, survival_succ]
      ring
    simpa only [hbudget] using h

/-- Almost-sure absorption is exactly the vanishing finite-horizon residual.
The continuation credit may be unbounded or infinite. -/
theorem twp_of_survival (E : CoPset) (e : ℕ → Exp rT) (Φ : Val rT → IProp GF)
    (q exit credit : ℕ → ℝ≥0∞)
    (conservation : ∀ n, credit n = exit n + q n * credit (n + 1))
    (step : ∀ n c, (⊢ ↯ c -∗ tglWp E (e (n + 1)) Φ) →
      ⊢ ↯ (exit n + q n * c) -∗ tglWp E (e n) Φ)
    (start : ℕ) (nonvalue : (e start).toVal? = none)
    (absorbs : Filter.Tendsto (survival q start) Filter.atTop (nhds 0)) :
    ⊢ ↯ (credit start) -∗ tglWp E (e start) Φ := by
  have hlimit : Filter.liminf (fun depth => credit start + survival q start depth)
      Filter.atTop = credit start := by
    simpa using (tendsto_const_nhds.add absorbs).liminf_eq
  iintro Hcredit
  iapply (twp_err_liminf (l := Filter.atTop) (S := Set.univ)
    (ε := fun depth : ℕ => credit start + survival q start depth)
    Filter.univ_mem nonvalue)
  isplitl [Hcredit]
  · isimp only [hlimit]
    iexact Hcredit
  · iintro %depth - Hcredit
    iapply twp_finite E e Φ q exit credit conservation step start depth $$ Hcredit

end specification

end

end SampLib.AbsorbingChain
