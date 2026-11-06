import SampLib.Ddg

/-! # DDG execution under a caller capability

A rejection-capable traversal may use its caller's restart rule at a
leaf. The finite-horizon and residual argument retain that capability throughout.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.DdgContext

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS DdgCredits

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Cutoff paths spend one credit; all real transitions retain the caller capability. -/
theorem twp_finite (E : CoPset) (e : ℕ → ℕ → Exp rT) (Φ : Val rT → IProp GF)
    (columns : ℕ → List ℕ) (alive : ℕ → ℕ) (F : ℕ → ℝ≥0∞)
    (R : IProp GF)
    (step : ∀ h d,
      (∀ rank, rank < alive (d + 1) →
        R ⊢ ↯ (cutCredit columns F h (d + 1) rank) -∗ tglWp E (e (d + 1) rank) Φ) →
      ∀ rank, rank < alive d →
        R ⊢ ↯ (cutCredit columns F (h + 1) d rank) -∗ tglWp E (e d rank) Φ)
    (h d rank : ℕ) (hr : rank < alive d) :
    R ⊢ ↯ (cutCredit columns F h d rank) -∗ tglWp E (e d rank) Φ := by
  induction h generalizing d rank with
  | zero =>
    iintro HR Hcredit
    iexfalso
    iapply ErrorCredit.contradict (by simp [cutCredit]) $$ Hcredit
  | succ h ih => exact step h d (fun rank hr => ih (d + 1) rank hr) rank hr

/-- A caller restart rule is preserved while the DDG cutoff residual tends to zero. -/
theorem twp_of_columns (E : CoPset) (e : ℕ → ℕ → Exp rT) (Φ : Val rT → IProp GF)
    (columns : ℕ → List ℕ) (alive : ℕ → ℕ) (F : ℕ → ℝ≥0∞)
    (width : ∀ d, 2 * alive d = (columns d).sum + alive (d + 1))
    (row : ℕ → ℝ≥0∞)
    (conservation : ∀ d, row d = (WeightedChoice.weightedSum (columns d) F + row (d + 1)) / 2)
    (bound : ℕ) (bounded : ∀ d, alive d ≤ bound) (root : alive 0 = 1)
    (R : IProp GF)
    (step : ∀ h d,
      (∀ rank, rank < alive (d + 1) →
        R ⊢ ↯ (cutCredit columns F h (d + 1) rank) -∗ tglWp E (e (d + 1) rank) Φ) →
      ∀ rank, rank < alive d →
        R ⊢ ↯ (cutCredit columns F (h + 1) d rank) -∗ tglWp E (e d rank) Φ)
    (nonvalue : (e 0 0).toVal? = none) :
    R ⊢ ↯ (row 0) -∗ tglWp E (e 0 0) Φ := by
  have hresidual : Filter.Tendsto (fun h : ℕ => (bound : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ h)
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
      (Or.inr (by simp : (bound : ℝ≥0∞) ≠ ∞))
  have hlimit : Filter.liminf (fun h : ℕ => row 0 + bound * (1 / 2 : ℝ≥0∞) ^ h)
      Filter.atTop = row 0 := by
    simpa using (tendsto_const_nhds.add hresidual).liminf_eq
  iintro HR Hcredit
  iapply (twp_err_liminf (l := Filter.atTop) (S := Set.univ)
    (ε := fun h : ℕ => row 0 + bound * (1 / 2 : ℝ≥0∞) ^ h)
    Filter.univ_mem nonvalue)
  isplitl [Hcredit]
  · isimp only [hlimit]
    iexact Hcredit
  · iintro %h - Hcredit
    have hbound := aggregate_le columns alive width F row conservation bound bounded h 0
    simp only [root, Finset.sum_range_one] at hbound
    ihave Hsample := ErrorCredit.weaken hbound $$ Hcredit
    iapply twp_finite E e Φ columns alive F R step h 0 0 (by rw [root]; omega) $$ HR Hsample

end

end SampLib.DdgContext
