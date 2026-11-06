import SampLib.Samplers.ExpMinusShifted
import SampLib.Samplers.OneMinusOverOnePlus
import Samplers.Bernoulli.Elementary

/-! # The shifted half-hyperbolic-tangent factory (derived) -/

open ProbLang
open scoped ENNReal

namespace SampLib.TanhHalfShifted

noncomputable section

def bias (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  OneMinusOverOnePlus.bias (ExpMinusShifted.bias p a b ha hb)

theorem bias_coe (p : unitInterval) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    (bias p a b ha hb : ℝ) = Real.tanh (((a : ℝ) / b + (p : ℝ)) / 2) := by
  simp only [bias, OneMinusOverOnePlus.bias, ExpMinusShifted.bias_coe]
  rw [Real.tanh_eq]
  have he : Real.exp (-((a : ℝ) / b + (p : ℝ))) =
      (Real.exp (((a : ℝ) / b + (p : ℝ)) / 2))⁻¹ *
        (Real.exp (((a : ℝ) / b + (p : ℝ)) / 2))⁻¹ := by
    rw [show -((a : ℝ) / b + (p : ℝ)) =
      -(((a : ℝ) / b + (p : ℝ)) / 2) + -(((a : ℝ) / b + (p : ℝ)) / 2) by ring,
      Real.exp_add, Real.exp_neg]
  rw [he, Real.exp_neg]
  field_simp

private def exponentialCoin {rT : Type} (coin : Val rT) (a b : ℤ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.expMinusShifted &coin.fst #int a #int b #()),
    .lam (by is_lc), by is_lc⟩

private theorem factory_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.oneMinusOverOnePlus =
      Occil.FactoryExtra.oneMinusOverOnePlus := (Exp.open_lc k e _ (by is_lc)).symm

private theorem factory_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.oneMinusOverOnePlus : Exp rT) =
      Occil.FactoryExtra.oneMinusOverOnePlus :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.oneMinusOverOnePlus, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem exponentialCoin_spec (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin coin a b).fst #())
      (RealCoin.law (ExpMinusShifted.bias p a b ha hb)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [ExpMinusShifted.expMinusShifted_openRec]
    iapply (ExpMinusShifted.expMinusShifted_distSpec E p a b ha hb coin hcoin).spec F hF
      $$ Hcredit

/-- Apply the verified reciprocal ratio to the actual shifted exponential callback. -/
theorem twp_tanhHalfShifted (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias p a b ha hb)) -∗
      tglWp E pl(&Occil.FactoryExtra.tanhHalfShifted &coin.fst #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hfactory := OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec (GF := GF) E
    (ExpMinusShifted.bias p a b ha hb) (exponentialCoin coin a b)
    (exponentialCoin_spec E p a b ha hb coin hcoin)
  simp only [exponentialCoin] at hfactory
  iintro Hcredit
  iterate 4 twp_pure
  isimp only [factory_open, factory_close, ExpMinusShifted.expMinusShifted_openRec,
    ExpMinusShifted.expMinusShifted_closeRec]
  isimp only [bias] at Hcredit
  iapply hfactory.spec F (measurable_of_finite _) $$ Hcredit

/-- The bias is tanh((a/b+p)/2), including zero shift and both input endpoints. -/
theorem tanhHalfShifted_distSpec (E : CoPset) (p : unitInterval) (a b : ℤ)
    (ha : 0 ≤ a) (hb : 0 < b) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.tanhHalfShifted &coin.fst #int a #int b #())
      (RealCoin.law (bias p a b ha hb)) Val.bool where
  spec F _ := wand_entails (twp_tanhHalfShifted E p a b ha hb coin hcoin F)

end specification

end

end SampLib.TanhHalfShifted
