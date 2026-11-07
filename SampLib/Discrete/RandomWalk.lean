import SampLib.Discrete.Laws.RandomWalk
import SampLib.Uniform.FairCoin
import Samplers.Discrete
import Metrology.Iris.LocalBI

/-! # Symmetric random walk

The law is the `n`-fold convolution of the symmetric distribution on `{-1, 1}`.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.RandomWalk

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_randomWalk (E : CoPset) (n : ℕ) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law n) -∗ tglWp E pl(&Occil.randomWalk #int (n : ℤ))
      (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  induction n generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [expectation_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.randomWalk #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation n F] at Hcredit
      iapply IH $$ Hcredit
    iintro %v ⟨%z, %hv, Hcredit⟩
    subst v
    twp_pure
    simp only [FairCoin.fairCoin_closeRec, FairCoin.fairCoin_openRec]
    twp_bind pl(&Occil.fairCoin #())
    isimp only [continuation] at Hcredit
    iapply ((FairCoin.fairCoin_distSpec E).wp
      (fun b => F (if b then z + 1 else z - 1)) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists (z - 1)
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pures
      twp_value
      imodintro
      iexists (z + 1)
      isimp only [ite_true] at Hcredit
      iframe Hcredit
      itrivial

/-- Typed specification for a symmetric walk of any finite length. -/
theorem randomWalk_distSpec (E : CoPset) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.randomWalk #int (n : ℤ)) (law n) Val.int where
  spec F _ := wand_entails (twp_randomWalk E n F)

end specification

end

end SampLib.RandomWalk
