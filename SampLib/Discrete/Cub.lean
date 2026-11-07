import SampLib.Discrete.Laws.Cub
import SampLib.Discrete.BinomialBinary
import SampLib.Uniform.RationalCoin
import SampLib.Continuous.Mixture
import Samplers.Discrete.Compound
import Metrology.Iris.LocalBI

/-! # The CUB mixture of ordinal responses

With probability `p`, return one plus a binomial count with success bias `1-ξ`;
otherwise return a uniform category in `1,…,m`.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Cub

noncomputable section

private instance binary_closed {rT : Type _} :
    ClosedExp (Occil.DiscreteExtra.binomialBinary : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.DiscreteExtra.binomialBinary, ClosedExp.closeRec, Exp.fv, ClosedExp.fv]

private theorem size_test (m : ℕ) (hm : 3 ≤ m) : decide ((m : ℤ) < 3) = false :=
  decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem selector_distSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) (ha : a ≤ b) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int (a : ℤ) #int (b : ℤ))
      (RealCoin.law (BinomialBinary.bias a b)) Val.bool := by
  have h := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF)
    E a b (by omega) (by omega) (by omega)
  simpa only [rational_bias a b hb ha] using h

private theorem component_distSpec (E : CoPset) (m c d : ℕ) (hd : 0 < d) (hc : c ≤ d) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.binomialBinary
      #int ((m - 1 : ℕ) : ℤ) #int ((d - c : ℕ) : ℤ) #int (d : ℤ))
      (Binomial.law (unitInterval.symm (BinomialBinary.bias c d)) (m - 1))
      (fun k : ℕ => Val.int (k : ℤ)) := by
  have h := BinomialBinary.binomialBinary_distSpec (rT := rT) (GF := GF)
    E (m - 1) (d - c) d hd (by omega)
  simpa only [BinomialBinary.law, complement_bias c d hd hc] using h

/-- CTE composition of the selector, shifted binomial, and uniform response. -/
theorem twp_cub (E : CoPset) (m a b c d : ℕ) (hm : 3 ≤ m) (hb : 0 < b)
    (ha : a ≤ b) (hd : 0 < d) (hc : c ≤ d) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law m (BinomialBinary.bias a b) (BinomialBinary.bias c d)) -∗
      tglWp E pl(&Occil.DiscreteExtra.cub #int (m : ℤ) #int (a : ℤ)
        #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  let _ : NeZero m := ⟨by omega⟩
  iintro Hcredit
  iterate 6 twp_pure
  rw [size_test m hm]
  twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec, RationalCoin.rationalCoin_openRec,
    RationalCoin.rationalCoin_closeRec, UniformInt.uniformInt_openRec,
    UniformInt.uniformInt_closeRec]
  twp_bind pl(&Occil.rationalCoin #int (a : ℤ) #int (b : ℤ))
  isimp only [expectation m _ _ (by omega), ← RealCoin.lintegral_law] at Hcredit
  iapply ((selector_distSpec E a b hb ha).wp _ (measurable_of_countable _) _) $$ Hcredit
  iintro %selected Hcredit
  cases selected
  · twp_pure
    isimp only [Bool.false_eq_true, ite_false] at Hcredit
    twp_bind pl(&Occil.uniformInt #int (m : ℤ))
    iapply ((UniformInt.uniformInt_distSpec E m).wp
      (fun k => F (k + 1)) (measurable_of_countable _) _) $$ Hcredit
    iintro %k Hcredit
    twp_pures
    rw [add_comm (1 : ℤ), ← Nat.cast_add_one]
    twp_value
    imodintro
    iexists k + 1
    iframe Hcredit
    itrivial
  · twp_pure
    isimp only [ite_true] at Hcredit
    iterate 2 twp_pure
    rw [show (d : ℤ) - c = ((d - c : ℕ) : ℤ) from (Nat.cast_sub hc).symm,
      show (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by omega]
    twp_bind pl(&Occil.DiscreteExtra.binomialBinary #int ((m - 1 : ℕ) : ℤ)
      #int ((d - c : ℕ) : ℤ) #int (d : ℤ))
    iapply ((component_distSpec E m c d hd hc).wp
      (fun k => F (k + 1)) (measurable_of_countable _) _) $$ Hcredit
    iintro %k Hcredit
    twp_pures
    rw [add_comm (1 : ℤ), ← Nat.cast_add_one]
    twp_value
    imodintro
    iexists k + 1
    iframe Hcredit
    itrivial

/-- Typed CUB law for every valid rational mixture and uncertainty bias. -/
theorem cub_distSpec (E : CoPset) (m a b c d : ℕ) (hm : 3 ≤ m) (hb : 0 < b)
    (ha : a ≤ b) (hd : 0 < d) (hc : c ≤ d) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.cub #int (m : ℤ) #int (a : ℤ)
      #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
      (law m (BinomialBinary.bias a b) (BinomialBinary.bias c d))
      (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_cub E m a b c d hm hb ha hd hc F)

end specification

end

end SampLib.Cub
