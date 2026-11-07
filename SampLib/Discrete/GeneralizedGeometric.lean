import SampLib.Discrete.Laws.GeneralizedGeometric
import SampLib.Common.AbsorbingChain
import SampLib.Uniform.RealCoin
import Samplers.Discrete.Tails

/-! # First stopping index for an indexed continuation coin

The input supplies a coin at each positive integer. The complete termination
condition is that its survival product tends to zero; no moment bound is needed.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.GeneralizedGeometric

noncomputable section

open MeasureTheory (lintegral_map)

private def loop {rT : Type _} (coin : Val rT) : Exp rT :=
  .fix (.lam (pl% if &coin.fst {Exp.bvar 0} then
    {Exp.bvar 1} ({Exp.bvar 0} + #1) else {Exp.bvar 0}))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def post (F : ℕ → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))

private theorem twp_loop_step (E : CoPset) (p : ℕ → unitInterval) (coin : Val rT)
    (hcoin : ∀ n : ℕ, IsDistSpec (GF := GF) E
      pl(&coin.fst #int ((n + 1 : ℕ) : ℤ)) (RealCoin.law (p n)) Val.bool)
    (F : ℕ → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞)
    (next : ⊢ ↯ c -∗ tglWp E pl(&(loop coin) #int ((n + 2 : ℕ) : ℤ))
      (post F)) :
    ⊢ ↯ ((1 - continuation p n) * F (n + 1) + continuation p n * c) -∗
      tglWp E pl(&(loop coin) #int ((n + 1 : ℕ) : ℤ))
        (post F) := by
  iintro Hcredit
  twp_pures
  twp_bind pl(&coin.fst #int ((n + 1 : ℕ) : ℤ))
  isimp only [← expectation p (fun k => F (k + 1)) n c] at Hcredit
  iapply ((hcoin n).wp (kernel (fun k => F (k + 1)) n c) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pures
    twp_value
    imodintro
    isimp only [post]
    iexists (n + 1)
    isimp only [kernel, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iterate 2 twp_pure
    rw [← Nat.cast_add_one, show n + 1 + 1 = n + 2 by omega]
    isimp only [kernel, ite_true] at Hcredit
    simp only [loop] at next
    iapply next $$ Hcredit

/-- All finite-horizon residuals vanish by the supplied survival criterion. -/
private theorem twp_loop (E : CoPset) (p : ℕ → unitInterval) (coin : Val rT)
    (hcoin : ∀ n : ℕ, IsDistSpec (GF := GF) E
      pl(&coin.fst #int ((n + 1 : ℕ) : ℤ)) (RealCoin.law (p n)) Val.bool)
    (F : ℕ → ℝ≥0∞) (start : ℕ)
    (absorbs : Filter.Tendsto (AbsorbingChain.survival (continuation p) start)
      Filter.atTop (nhds 0)) :
    ⊢ ↯ (∫⁻ n, F (n + 1) ∂AbsorbingChain.stopLaw (continuation p) start) -∗
      tglWp E pl(&(loop coin) #int ((start + 1 : ℕ) : ℤ))
        (post F) := by
  apply AbsorbingChain.twp_of_survival E
    (fun n => pl(&(loop coin) #int ((n + 1 : ℕ) : ℤ))) _ (continuation p)
    (fun n => (1 - continuation p n) * F (n + 1))
    (fun n => ∫⁻ k, F (k + 1) ∂AbsorbingChain.stopLaw (continuation p) n)
    (fun n => AbsorbingChain.stopLaw_expectation _ n (fun k => F (k + 1)))
    (twp_loop_step E p coin hcoin F) start rfl absorbs

/-- Typed law for every indexed coin family whose survival probability vanishes. -/
theorem generalizedGeometric_distSpec (E : CoPset) (p : ℕ → unitInterval)
    (coin : Val rT)
    (hcoin : ∀ n : ℕ, IsDistSpec (GF := GF) E
      pl(&coin.fst #int ((n + 1 : ℕ) : ℤ)) (RealCoin.law (p n)) Val.bool)
    (absorbs : Filter.Tendsto (AbsorbingChain.survival (continuation p) 0)
      Filter.atTop (nhds 0)) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.generalizedGeometric &coin.fst)
      (law p absorbs) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := by
    iintro Hcredit
    isimp only [law, lintegral_map (measurable_of_countable _)
      (measurable_of_countable _), Nat.succ_eq_add_one] at Hcredit
    iterate 2 twp_pure
    have h := twp_loop E p coin hcoin F 0 absorbs
    simp only [loop, Nat.zero_add, Nat.cast_one] at h
    unfold post at h
    iapply h $$ Hcredit

end specification

end

end SampLib.GeneralizedGeometric
