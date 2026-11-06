import SampLib.LinearFactorySyntax
import SampLib.FactorySyntax

/-! # Independent powers of the linear factory

This named construction derives its power law by finite iteration of the verified
linear callback. Zero iterations inspect neither its parameters nor the callback.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LinearPower

noncomputable section

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.linearPower, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.linearPower := rfl

private def callback {rT : Type _} (coin : Val rT) (a b e f : ℤ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.linear &coin.fst #int a #int b #int e #int f #()),
    .lam (by is_lc), by is_lc⟩

private theorem zero_expectation (F : Bool → ℝ≥0∞) :
    (∫⁻ z, F z ∂RealCoin.law 1) = F true := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Zero powers do not require valid factory parameters or an input-coin contract. -/
theorem linearPower_zero_distSpec (E : CoPset) (coin : Val rT) (a b e f : ℤ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linearPower &coin.fst #int a #int b #0 #int e #int f #())
      (RealCoin.law 1) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 14 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close,
      Exp.closeRec, Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst,
      LinearFactorySyntax.linear_openRec, LinearFactorySyntax.linear_closeRec,
      FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec])
    twp_value
    imodintro
    iexists true
    isimp only [zero_expectation] at Hcredit
    iframe Hcredit
    itrivial

variable [ProbLangDist.IsUniformInt rT]

private theorem callback_spec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(callback coin a b e f).fst #())
      (RealCoin.law (LinearFactory.bias p a b e f h)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_step
    simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst, LinearFactorySyntax.linear_openRec]
    iapply (LinearFactory.linear_distSpec E p a b e f h coin hcoin).spec F hF $$ Hcredit

/-- Derived power law over the complete domain of the underlying linear factory. -/
theorem linearPower_distSpec (E : CoPset) (p : unitInterval) (a b e f : ℤ)
    (h : LinearFactory.Admissible p a b e f) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.linearPower &coin.fst #int a #int b #int (n : ℤ) #int e #int f #())
      (IterateCoin.law (LinearFactory.bias p a b e f h) n) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 9 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close,
      Exp.closeRec, Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst,
      LinearFactorySyntax.linear_openRec, LinearFactorySyntax.linear_closeRec,
      FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec])
    twp_bind pl(&Occil.iterateCoin &(callback coin a b e f).fst #int (n : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (IterateCoin.iterateCoin_distSpec E _ (callback coin a b e f)
      (callback_spec E p a b e f h coin hcoin) n).spec F (measurable_of_countable _) $$ Hcredit

end specification

end

end SampLib.LinearPower
