import SampLib.AbsorbingChain

/-! # Absorbing chains with a state-dependent postcondition

The current state may shift the returned count or retain a mathematical invariant.
As in the fixed-postcondition rule, the only approximation is the survival mass.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AbsorbingChain

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_finite_indexed (E : CoPset) (e : ℕ → Exp rT)
    (Φ : ℕ → Val rT → IProp GF) (q exit credit : ℕ → ℝ≥0∞)
    (conservation : ∀ n, credit n = exit n + q n * credit (n + 1))
    (step : ∀ n c, (⊢ ↯ c -∗ tglWp E (e (n + 1)) (Φ (n + 1))) →
      ⊢ ↯ (exit n + q n * c) -∗ tglWp E (e n) (Φ n)) (start depth : ℕ) :
    ⊢ ↯ (credit start + survival q start depth) -∗ tglWp E (e start) (Φ start) := by
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

/-- Vanishing survival proves total correctness even when recursive return
credits and invariants depend on the current state. -/
theorem twp_of_survival_indexed (E : CoPset) (e : ℕ → Exp rT)
    (Φ : ℕ → Val rT → IProp GF) (q exit credit : ℕ → ℝ≥0∞)
    (conservation : ∀ n, credit n = exit n + q n * credit (n + 1))
    (step : ∀ n c, (⊢ ↯ c -∗ tglWp E (e (n + 1)) (Φ (n + 1))) →
      ⊢ ↯ (exit n + q n * c) -∗ tglWp E (e n) (Φ n))
    (start : ℕ) (nonvalue : (e start).toVal? = none)
    (absorbs : Filter.Tendsto (survival q start) Filter.atTop (nhds 0)) :
    ⊢ ↯ (credit start) -∗ tglWp E (e start) (Φ start) := by
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
    iapply twp_finite_indexed E e Φ q exit credit conservation step start depth $$ Hcredit

end

end SampLib.AbsorbingChain
