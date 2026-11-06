import SampLib.Distributions.CriticalCoinKernel
import SampLib.Templates

/-! # Finite-horizon CTE induction for critical coin recursion

The program-specific step executes one layer using the two finite-depth calls.
The exact unresolved mass vanishes, so the resulting specification needs no
geometric contraction or finite expected running time.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.CriticalCoin

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Finite-tree induction leaves one error-credit unit on each unresolved branch. -/
theorem twp_finite (E : CoPset) (e : ℕ → Exp rT) (a : ℕ → Coefficient) (states : Set ℕ)
    (step : ∀ n, (∀ i, i ∈ states → ∀ (F : Bool → ℝ≥0∞),
      ⊢ ↯ (credit a n i F) -∗ tglWp E (e i)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) →
      ∀ i, i ∈ states → ∀ (F : Bool → ℝ≥0∞),
        ⊢ ↯ (credit a (n + 1) i F) -∗ tglWp E (e i)
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (n i : ℕ) (hi : i ∈ states) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit a n i F) -∗ tglWp E (e i)
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction n generalizing i F with
  | zero =>
    iintro Hcredit
    isimp only [credit_zero] at Hcredit
    iexfalso
    iapply ErrorCredit.contradict le_rfl $$ Hcredit
  | succ n IH => exact step n IH i hi F

/-- Vanishing unresolved mass turns the finite trees into the canonical fraction law. -/
theorem distSpec_of_finite (E : CoPset) (e : ℕ → Exp rT) (a : ℕ → Coefficient) (states : Set ℕ)
    (step : ∀ n, (∀ i, i ∈ states → ∀ (F : Bool → ℝ≥0∞),
      ⊢ ↯ (credit a n i F) -∗ tglWp E (e i)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) →
      ∀ i, i ∈ states → ∀ (F : Bool → ℝ≥0∞),
        ⊢ ↯ (credit a (n + 1) i F) -∗ tglWp E (e i)
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (i : ℕ) (hi : i ∈ states) (nonvalue : (e i).toVal? = none) :
    IsDistSpec (GF := GF) E (e i) (RealCoin.law (bias a i)) Val.bool where
  spec F _ := by
    have hlimit := (credit_tendsto a i F).liminf_eq
    iintro Hcredit
    isimp only [RealCoin.lintegral_law] at Hcredit
    iapply (twp_err_liminf (l := Filter.atTop) (S := Set.univ)
      (ε := fun n : ℕ => credit a n i F) Filter.univ_mem nonvalue)
    isplitl [Hcredit]
    · isimp only [hlimit]
      iexact Hcredit
    · iintro %n - Hcredit
      iapply twp_finite E e a states step n i hi F $$ Hcredit

end specification

end

end SampLib.CriticalCoin
