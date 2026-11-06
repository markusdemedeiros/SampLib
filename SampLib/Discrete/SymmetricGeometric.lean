import SampLib.Discrete.Laws.SymmetricGeometric
import SampLib.Discrete.Geometric
import SampLib.Bernoulli.OneDivOnePlus
import SampLib.Common.CoinComplement
import Samplers.Discrete.Tails

/-! # Two-sided geometric sampling

The CTE proof draws a geometric magnitude, then a reciprocal side selector, and
places the magnitude on the selected side of zero.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SymmetricGeometric

noncomputable section

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.geometric = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem reciprocal_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.oneDivOnePlus = Occil.oneDivOnePlus :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem reciprocal_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.oneDivOnePlus : Exp rT) = Occil.oneDivOnePlus :=
  Exp.closeRec_fresh x _ k (by simp [Occil.oneDivOnePlus, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The signed geometric law from any coin with positive success probability. -/
theorem twp_symmetricGeometric (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law p) -∗
      tglWp E pl(&Occil.DiscreteExtra.symmetricGeometric &coin.fst #())
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iterate 2 twp_pure
  simp only [geometric_close, geometric_open, reciprocal_close, reciprocal_open]
  twp_bind pl(&Occil.geometric &coin.fst #())
  isimp only [← expectation p F] at Hcredit
  iapply ((Geometric.geometric_distSpec E p hp coin hcoin).wp (continuation p F)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  twp_pure
  twp_bind pl(&Occil.oneDivOnePlus &(CoinComplement.callback coin).fst #())
  isimp only [continuation] at Hcredit
  iapply ((OneDivOnePlus.oneDivOnePlus_distSpec E (unitInterval.symm p)
    (CoinComplement.callback coin)
    (CoinComplement.distSpec E p coin hcoin)).wp (fun b => F (signed n b))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b <;> twp_pures <;> twp_value <;> imodintro
  · iexists (-1 - (n : ℤ))
    isimp only [signed, Bool.false_eq_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  · iexists (n : ℤ)
    isimp only [signed, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Typed two-sided geometric specification, including the deterministic endpoint. -/
theorem symmetricGeometric_distSpec (E : CoPset) (p : unitInterval) (hp : 0 < (p : ℝ))
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.symmetricGeometric &coin.fst #())
      (law p) Val.int where
  spec F _ := wand_entails (twp_symmetricGeometric E p hp coin hcoin F)

end specification

end

end SampLib.SymmetricGeometric
