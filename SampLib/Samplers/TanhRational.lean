import SampLib.Samplers.ExpMinusRational
import SampLib.Samplers.OneMinusOverOnePlus
import Samplers.Bernoulli.Elementary

/-! # Hyperbolic-tangent coins for nonnegative rational inputs -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.TanhRational

noncomputable section

/-- Apply `(1-p)/(1+p)` to `p=exp(-2a/b)`. -/
def bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) : unitInterval :=
  OneMinusOverOnePlus.bias
    (ExpMinusRational.bias (2 * a) b (mul_nonneg (by decide) ha) hb)

/-- The rational exponential ratio is the hyperbolic tangent. -/
theorem coe_bias (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    (bias a b ha hb : ℝ) = Real.tanh ((a : ℝ) / b) := by
  simp only [bias, OneMinusOverOnePlus.bias, ExpMinusRational.bias, Int.cast_mul,
    Int.cast_ofNat]
  rw [Real.tanh_eq]
  have he : Real.exp (-(2 * (a : ℝ)) / b) =
      (Real.exp ((a : ℝ) / b))⁻¹ * (Real.exp ((a : ℝ) / b))⁻¹ := by
    rw [show -(2 * (a : ℝ)) / b = -((a : ℝ) / b) + -((a : ℝ) / b) by ring,
      Real.exp_add, Real.exp_neg]
  rw [he, Real.exp_neg]
  field_simp

@[local simp] private theorem factory_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.oneMinusOverOnePlus =
      Occil.FactoryExtra.oneMinusOverOnePlus := (Exp.open_lc k e _ (by is_lc)).symm

@[local simp] private theorem factory_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.oneMinusOverOnePlus : Exp rT) =
      Occil.FactoryExtra.oneMinusOverOnePlus :=
  Exp.closeRec_fresh x _ k (by
    simp [Occil.FactoryExtra.oneMinusOverOnePlus, Exp.fv, FairCoin.fairCoin_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def exponentialCoin (a b : ℤ) : Val rT :=
  ⟨pl(fun u, &Occil.expMinusRational (#2 * #int a) #int b #()),
    .lam (by is_lc), by is_lc⟩

private theorem exponentialCoin_spec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin a b).fst #())
      (RealCoin.law (ExpMinusRational.bias (2 * a) b (mul_nonneg (by decide) ha) hb))
      Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ExpMinusRational.expMinusRational_openRec,
      ExpMinusRational.expMinusRational_closeRec, Exp.ofVal]
    iapply (ExpMinusRational.expMinusRational_distSpec E (2 * a) b
      (mul_nonneg (by decide) ha) hb).spec F hF $$ Hcredit

/-- The outer factory receives the verified doubled-exponential callback. -/
theorem twp_tanhRational (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias a b ha hb)) -∗
      tglWp E pl(&Occil.FactoryExtra.tanhRational #int a #int b #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hfactory := OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec (GF := GF) E
    (ExpMinusRational.bias (2 * a) b (mul_nonneg (by decide) ha) hb)
    (exponentialCoin (rT := rT) a b) (exponentialCoin_spec E a b ha hb)
  simp [exponentialCoin, Exp.close, Exp.closeRec] at hfactory
  iintro Hcredit
  iterate 3 twp_pure
  simp only [factory_open, factory_close, ExpMinusRational.expMinusRational_openRec,
    ExpMinusRational.expMinusRational_closeRec]
  isimp only [bias] at Hcredit
  iapply hfactory.spec F (measurable_of_countable _) $$ Hcredit

theorem tanhRational_distSpec (E : CoPset) (a b : ℤ) (ha : 0 ≤ a) (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.tanhRational #int a #int b #())
      (RealCoin.law (bias a b ha hb)) Val.bool where
  spec F _ := wand_entails (twp_tanhRational E a b ha hb F)

end specification

end

end SampLib.TanhRational
