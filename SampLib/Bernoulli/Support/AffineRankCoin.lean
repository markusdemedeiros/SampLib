import SampLib.Bernoulli.Laws.OffsetRace
import SampLib.Uniform.UniformInt
import Metrology.Iris.LocalBI

/-! # Affine coins from three uniform-rank intervals

The interval expectation is shared with the offset race; this reusable callback
exposes its exact structural syntax without closing over a supplied coin's free names.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AffineRankCoin

noncomputable section

def body {rT : Type _} (coin : Val rT) (a s : ℕ) : Exp rT :=
  .cond (.binop .lt (.bvar 0) (.lit (.int a))) (.lit (.bool true))
    (.cond (.binop .lt (.bvar 0) (.binop .plus (.lit (.int a)) (.lit (.int s))))
      (.app coin.fst (.lit .unit)) (.lit (.bool false)))

/-- Certain success, one fresh input call, then certain failure. -/
def callback {rT : Type _} (coin : Val rT) (a s t : ℕ) : Val rT :=
  ⟨.lam (.app (.lam (body coin a s)) pl(&Occil.uniformInt #int (t : ℤ))),
    .lam (by unfold body; is_lc), by unfold body; is_lc⟩

private theorem lt_test (k n : ℕ) : decide ((k : ℤ) < n) = decide (k < n) := by
  simp only [Int.ofNat_lt]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable [ProbLangDist.IsUniformInt rT]
local bi (IProp GF)

/-- The three symbolic branches spend exactly the shared interval expectation. -/
theorem distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (a s t : ℕ) (ht : 0 < t) (hast : a + s ≤ t) :
    IsDistSpec (GF := GF) E pl(&(callback coin a s t).fst #())
      (RealCoin.law (OffsetRace.affineBias p a s t ht hast)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    simp only [UniformInt.uniformInt_openRec]
    twp_bind pl(&Occil.uniformInt #int (t : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply UniformInt.twp_uniformInt E t ht (OffsetRace.rankCredit p a s F)
      rw [OffsetRace.expectation p a s t ht hast F, ← RealCoin.lintegral_law]
      iexact Hcredit
    iintro %v ⟨%k, %hv, %hk, Hcredit⟩
    subst v
    simp [body, Exp.openRec]
    twp_pure
    twp_pures
    by_cases ha : k < a
    · rw [lt_test, decide_eq_true ha]
      twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [OffsetRace.rankCredit, ite_eq_left ha] at Hcredit
      iframe Hcredit
      itrivial
    · rw [lt_test, decide_eq_false ha]
      twp_pures
      by_cases hs : k < a + s
      · rw [← Nat.cast_add, lt_test, decide_eq_true hs]
        twp_pures
        isimp only [OffsetRace.rankCredit, ite_eq_right ha, ite_eq_left hs,
          ← RealCoin.lintegral_law] at Hcredit
        iapply hcoin.spec F (measurable_of_countable _) $$ Hcredit
      · rw [← Nat.cast_add, lt_test, decide_eq_false hs]
        twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [OffsetRace.rankCredit, ite_eq_right ha, ite_eq_right hs] at Hcredit
        iframe Hcredit
        itrivial

end specification

end

end SampLib.AffineRankCoin
