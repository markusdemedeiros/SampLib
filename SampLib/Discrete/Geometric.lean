import SampLib.Discrete.Laws.Geometric
import SampLib.Uniform.RealCoin
import SampLib.Core.Retry
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-!
# Geometric failures before the first success

The input coin is abstract. Success receives spare termination credit; failure
amplifies it by `1+p`. This treats `p=1` without a separate termination proof.
-/

open Set ProbLang
open scoped ENNReal NNReal

namespace SampLib.Geometric

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Geometric failure count from an abstract positive-probability coin. -/
theorem twp_geometric (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗ tglWp E pl(&Occil.geometric &coin.fst #())
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  irevert! %F
  iapply Retry.twp_loop_forall (fun _ => solve_not_value) (one_lt_terminationFactor p hp)
  iintro !> %ε %hε %F IH Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [← lintegral_coinCredit p hp F ε] at Hcredit
  iapply (hcoin.wp (coinCredit p F ε) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [coinCredit] at Hcredit
    twp_pure
    twp_bind pl(&Occil.geometric &coin.fst #())
    iapply tglWp_wand
    isplitl [IH Hcredit]
    · iapply IH $$ %(fun n => F (n + 1)) Hcredit
    iintro %v ⟨%n, %hv, Hcredit⟩
    subst v
    twp_pures
    rw [add_comm (1 : ℤ), ← Nat.cast_add_one]
    twp_value
    imodintro
    iexists n + 1
    iframe Hcredit
    itrivial
  · isimp only [coinCredit] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    iframe Hcredit
    itrivial

/-- Typed geometric distribution specification, including `p=1`. -/
theorem geometric_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.geometric &coin.fst #()) (law p)
      (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    simpa only [credit] using wand_entails (twp_geometric E p hp coin hcoin F)

end specification

end

end SampLib.Geometric
