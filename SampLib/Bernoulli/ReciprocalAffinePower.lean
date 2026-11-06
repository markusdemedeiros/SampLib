import SampLib.Bernoulli.ReciprocalAffine
import SampLib.Continuous.IterateCoin
import SampLib.Common.FactorySyntax

/-! # Powers of the reciprocal affine factory -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ReciprocalAffinePower


noncomputable section

private theorem zero_expectation (F : Bool → ℝ≥0∞) :
    (∫⁻ b, F b ∂RealCoin.law 1) = F true := by
  simp [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf]

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.reciprocalAffinePower, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.reciprocalAffinePower := rfl

private def callback {rT : Type _} (coin : Val rT) (a b x y : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.reciprocalAffine &coin.fst
    #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #()),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Zero repetitions return true without inspecting the rational parameters or input coin. -/
theorem reciprocalAffinePower_zero_distSpec (E : CoPset) (coin : Val rT) (a b x y : ℤ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.reciprocalAffinePower &coin.fst #int a #int b #int x #int y #0 #())
      (RealCoin.law 1) Val.bool where
  spec F _ := by
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 14 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close,
      Exp.closeRec, Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst,
      ReciprocalAffine.reciprocalAffine_openRec, ReciprocalAffine.reciprocalAffine_closeRec,
      FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec])
    twp_value
    imodintro
    iexists true
    isimp only [zero_expectation] at Hcredit
    iframe Hcredit
    itrivial

variable [ProbLangDist.IsUniformInt rT]

private theorem callback_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (a b x y : ℕ) (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hbound : x * b ≤ a * y)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(callback coin a b x y).fst #())
      (RealCoin.law (ReciprocalAffine.bias p (a * y) (x * b) (b * y)
        (Nat.mul_pos ha hy) hbound)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_step
    simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst,
      ReciprocalAffine.reciprocalAffine_openRec]
    iapply (ReciprocalAffine.reciprocalAffine_distSpec E p a b x y ha hb hy hbound coin hcoin).spec
      F hF $$ Hcredit

/-- Independent repetitions give the power of the reciprocal affine bias. -/
theorem twp_reciprocalAffinePower (E : CoPset) (p : unitInterval) (coin : Val rT)
    (a b x y k : ℕ) (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hbound : x * b ≤ a * y)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (IterateCoin.credit (ReciprocalAffine.bias p (a * y) (x * b) (b * y)
      (Nat.mul_pos ha hy) hbound) k F) -∗
      tglWp E pl(&Occil.FactoryExtra.reciprocalAffinePower &coin.fst
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #int (k : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  iintro Hcredit
  rw [← source_fst (rT := rT)]
  iterate 9 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close,
    Exp.closeRec, Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst,
    ReciprocalAffine.reciprocalAffine_openRec, ReciprocalAffine.reciprocalAffine_closeRec,
    FactorySyntax.iterateCoin_openRec, FactorySyntax.iterateCoin_closeRec])
  twp_bind pl(&Occil.iterateCoin &(callback coin a b x y).fst #int (k : ℤ))
  iapply (tglWp_mono fun _ => tglWp_value)
  iapply (IterateCoin.twp_iterateCoin E _ (callback coin a b x y)
    (callback_distSpec E p coin a b x y ha hb hy hbound hcoin) k F) $$ Hcredit

/-- Typed power law, including zero repetitions. -/
theorem reciprocalAffinePower_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (a b x y k : ℕ) (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) (hbound : x * b ≤ a * y)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.reciprocalAffinePower &coin.fst
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #int (k : ℤ) #())
      (IterateCoin.law (ReciprocalAffine.bias p (a * y) (x * b) (b * y)
        (Nat.mul_pos ha hy) hbound) k) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law, IterateCoin.law, IterateCoin.credit] using
      wand_entails (twp_reciprocalAffinePower E p coin a b x y k ha hb hy hbound hcoin F)

end specification

end

end SampLib.ReciprocalAffinePower
