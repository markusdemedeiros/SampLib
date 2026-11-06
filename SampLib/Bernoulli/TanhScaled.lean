import SampLib.Bernoulli.ExpMinusScaled
import SampLib.Bernoulli.OneMinusOverOnePlus
import Samplers.Bernoulli.Elementary

/-! # Hyperbolic-tangent factories for scaled input biases -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.TanhScaled

noncomputable section

/-- Apply `(1-q)/(1+q)` to `q=exp(-2(a/b)p)`. -/
def bias (p : unitInterval) (a b : ℕ) : unitInterval :=
  OneMinusOverOnePlus.bias
    (ExpMinusScaled.bias p (2 * a) b)

/-- The exponential ratio is the hyperbolic tangent of the scaled input bias. -/
theorem coe_bias (p : unitInterval) (a b : ℕ) :
    (bias p a b : ℝ) = Real.tanh ((a : ℝ) / b * (p : ℝ)) := by
  simp only [bias, OneMinusOverOnePlus.bias, ExpMinusScaled.bias, Nat.cast_mul,
    Nat.cast_ofNat]
  rw [Real.tanh_eq]
  have he : Real.exp (-(2 * (a : ℝ)) / b * (p : ℝ)) =
      (Real.exp ((a : ℝ) / b * (p : ℝ)))⁻¹ * (Real.exp ((a : ℝ) / b * (p : ℝ)))⁻¹ := by
    rw [show -(2 * (a : ℝ)) / b * (p : ℝ) =
      -((a : ℝ) / b * (p : ℝ)) + -((a : ℝ) / b * (p : ℝ)) by ring,
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

private def exponentialCoin (coin : Val rT) (a b : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.expMinusScaled &coin.fst (#2 * #int (a : ℤ))
    #int (b : ℤ) #()), .lam (by is_lc), by is_lc⟩

private theorem exponentialCoin_spec (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin coin a b).fst #())
      (RealCoin.law (ExpMinusScaled.bias p (2 * a) b)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ExpMinusScaled.expMinusScaled_openRec,
      Exp.ofVal]
    have hscaled := ExpMinusScaled.expMinusScaled_distSpec E p (2 * a) b hb coin hcoin
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hscaled
    iapply hscaled.spec F hF $$ Hcredit

/-- The outer factory receives the verified doubled-exponential callback. -/
theorem twp_tanhScaled (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias p a b)) -∗
      tglWp E pl(&Occil.FactoryExtra.tanhScaled &coin.fst #int (a : ℤ) #int (b : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have hfactory := OneMinusOverOnePlus.oneMinusOverOnePlus_distSpec (GF := GF) E
    (ExpMinusScaled.bias p (2 * a) b)
    (exponentialCoin coin a b) (exponentialCoin_spec E p a b hb coin hcoin)
  simp only [exponentialCoin] at hfactory
  iintro Hcredit
  iterate 4 twp_pure
  simp only [factory_open, factory_close, ExpMinusScaled.expMinusScaled_openRec,
    ExpMinusScaled.expMinusScaled_closeRec]
  isimp only [bias] at Hcredit
  iapply hfactory.spec F (measurable_of_countable _) $$ Hcredit

theorem tanhScaled_distSpec (E : CoPset) (p : unitInterval) (a b : ℕ) (hb : 0 < b)
    (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.tanhScaled &coin.fst #int (a : ℤ) #int (b : ℤ) #())
      (RealCoin.law (bias p a b)) Val.bool where
  spec F _ := wand_entails (twp_tanhScaled E p a b hb coin hcoin F)

end specification

end

end SampLib.TanhScaled
