import SampLib.Core.Laws.Retry
import Metrology.TotalEris.ErrorRules
import Metrology.Iris.LocalBI

/-! # Termination of retry loops by error amplification

A loop that retries with probability bounded away from one terminates. Its proof
draws a small positive credit `ε` and amplifies it by a factor `k > 1` on every
retry, until the credit reaches one. `twp_loop` packages that argument, so that a
caller proves only one round of the loop. `twp_loop_forall` lets the retry change
the loop's arguments.
-/

open Iris Iris.BI Iris.ProofMode ProbLang TotalEris ErisWpGS
open scoped ENNReal NNReal

namespace SampLib.Retry

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Retry by error amplification. To run the loop `e` with credit `c`, prove one
round for every `ε > 0`: from `↯ (c + ε)`, reach the postcondition, where a retry
may pay `↯ (c + k * ε)`. -/
theorem twp_loop {E : CoPset} {e : Exp rT} {Φ : Val rT → IProp GF} {c : ℝ≥0∞} {k : ℝ≥0}
    (hnv : e.toVal? = none) (hk : 1 < k) :
    □ (∀ ε, ⌜0 < ε⌝ -∗ (↯ (c + k * ε) -∗ tglWp E e Φ) -∗ ↯ (c + ε) -∗ tglWp E e Φ) ⊢
      ↯ c -∗ tglWp E e Φ := by
  iintro #Hround Hc
  iapply twp_err_pos hnv
  iintro %ε %hε Hε
  irevert Hc
  iapply ErrorCredit.Induction.simple hε hk $$ [] Hε
  iintro !> ⟨IH, Hε⟩ Hc
  icombine Hc Hε as Hc
  iapply Hround $$ %ε %hε [IH] Hc
  iintro Hc
  ihave ⟨Hc, Hε⟩ := ErrorCredit.split $$ Hc
  iapply IH $$ Hε Hc

/-- `twp_loop` for a loop family `e i`, where a retry may continue at any index. -/
theorem twp_loop_forall {E : CoPset} {ι : Type _} {e : ι → Exp rT}
    {Φ : ι → Val rT → IProp GF} {c : ι → ℝ≥0∞} {k : ℝ≥0}
    (hnv : ∀ i, (e i).toVal? = none) (hk : 1 < k) :
    □ (∀ ε, ⌜0 < ε⌝ -∗ ∀ i, (∀ j, ↯ (c j + k * ε) -∗ tglWp E (e j) (Φ j)) -∗
        ↯ (c i + ε) -∗ tglWp E (e i) (Φ i)) ⊢
      ∀ i, ↯ (c i) -∗ tglWp E (e i) (Φ i) := by
  iintro #Hround %i Hc
  iapply twp_err_pos (hnv i)
  iintro %ε %hε Hε
  irevert %i Hc
  iapply ErrorCredit.Induction.simple hε hk $$ [] Hε
  iintro !> ⟨IH, Hε⟩ %i Hc
  icombine Hc Hε as Hc
  iapply Hround $$ %ε %hε %i [IH] Hc
  iintro %j Hc
  ihave ⟨Hc, Hε⟩ := ErrorCredit.split $$ Hc
  iapply IH $$ Hε %j Hc

end SampLib.Retry
