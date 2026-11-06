import SampLib.Samplers.PolyaEggenberger
import Samplers.Discrete.Urns

/-! # Beta-binomial sampling with rational shapes

Clearing the two shape denominators gives an integer reinforced urn. Its
rising-product word probabilities are the beta-binomial mixture weights.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.BetaBinomial

set_option maxHeartbeats 1000000

noncomputable section

/-- Beta-binomial count with shapes `a/b` and `c/d`. -/
def law (n a b c d : ℕ) := PolyaEggenberger.law n (a * d) (c * b) (b * d)

instance (n a b c d : ℕ) : MeasureTheory.IsProbabilityMeasure (law n a b c d) := by
  unfold law
  infer_instance

private theorem polya_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.polyaEggenberger = Occil.polyaEggenberger :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem polya_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.polyaEggenberger : Exp rT) = Occil.polyaEggenberger :=
  Exp.closeRec_fresh x _ k (by simp [Occil.polyaEggenberger, Exp.fv, RationalCoin.rationalCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem valid_test (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    (((decide ((a : ℤ) ≤ 0) || decide ((b : ℤ) ≤ 0)) || decide ((c : ℤ) ≤ 0)) ||
      decide ((d : ℤ) ≤ 0)) = false := by simp [ha.ne', hb.ne', hc.ne', hd.ne']

/-- Clear the rational denominators, then apply the verified reinforced-urn sampler. -/
theorem twp_betaBinomial (E : CoPset) (n a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n a b c d) -∗
      tglWp E pl(&Occil.DiscreteExtra.betaBinomial #int (n : ℤ)
        #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  twp_pures
  rw [valid_test a b c d ha hb hc hd]
  iterate 4 twp_pure
  simp only [polya_open, polya_close, Exp.ofVal]
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]
  isimp only [law] at Hcredit
  iapply (PolyaEggenberger.twp_polyaEggenberger E n (a * d) (c * b) (b * d)
    (Or.inr (by positivity)) F) $$ Hcredit

/-- Typed beta-binomial law for positive rational shapes and every trial count. -/
theorem betaBinomial_distSpec (E : CoPset) (n a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.betaBinomial #int (n : ℤ)
      #int (a : ℤ) #int (b : ℤ) #int (c : ℤ) #int (d : ℤ))
      (law n a b c d) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_betaBinomial E n a b c d ha hb hc hd F)

end specification

end

end SampLib.BetaBinomial
