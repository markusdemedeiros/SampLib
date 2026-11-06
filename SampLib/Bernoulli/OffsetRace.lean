import SampLib.Core.SamplerStep
import SampLib.Common.FactorySyntax
import SampLib.Bernoulli.BernoulliRace
import SampLib.Bernoulli.Laws.OffsetRace
import SampLib.Bernoulli.Support.AffineRankCoin
import Samplers.Bernoulli.Rational

/-! # Bernoulli races with rational offsets

Each side samples a uniform rank in three intervals: certain success, a fresh
input coin, or certain failure. Racing the resulting affine coins cancels their
common normalization.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.OffsetRace

noncomputable section

private theorem race_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.bernoulliRace = Occil.bernoulliRace :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem race_close {rT : Type _} (k : ℕ) (v : Var) :
    Exp.closeRec k v (Occil.bernoulliRace : Exp rT) = Occil.bernoulliRace :=
  Exp.closeRec_fresh v _ k (by
    simp [Occil.bernoulliRace, Exp.fv, FairCoin.fairCoin_fv])

private theorem nonpositive_test (n : ℕ) (hn : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast Nat.not_le.mpr hn)

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.offsetRace, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.offsetRace := rfl

section specification

open FactorySyntax
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Construct the two affine callbacks and invoke the verified Bernoulli race. -/
theorem twp_offsetRace (E : CoPset) (p q : unitInterval) (a b x y : ℕ)
    (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ))
    (pcoin qcoin : Val rT)
    (hpcoin : IsDistSpec (GF := GF) E pl(&pcoin.fst #()) (RealCoin.law p) Val.bool)
    (hqcoin : IsDistSpec (GF := GF) E pl(&qcoin.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂RealCoin.law (bias p q a b x y hb hy)) -∗
      tglWp E pl(&Occil.FactoryExtra.offsetRace &pcoin.fst &qcoin.fst
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  rw [← source_fst]
  iterate 7 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close, Exp.closeRec,
    Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst, race_open, race_close,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec])
  twp_pures
  simp only [nonpositive_test b hb, nonpositive_test y hy, Bool.or_false]
  iterate 12 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.ofVal,
    ProbLang.openRec_val_fst, race_open, UniformInt.uniformInt_openRec])
  simp only [← Nat.cast_mul, ← Nat.cast_add]
  isimp only [bias] at Hcredit
  have hrace := BernoulliRace.bernoulliRace_distSpec (GF := GF) E
    (leftBias q a b x y hb hy) (rightBias p a b x y hb hy) (race_pos p q a b x y hb hy h)
    (AffineRankCoin.callback qcoin (x * b) (b * y) (total a b x y))
    (AffineRankCoin.callback pcoin (a * y) (b * y) (total a b x y))
    (AffineRankCoin.distSpec E q qcoin hqcoin (x * b) (b * y) (total a b x y)
      (total_pos a b x y hb hy) (left_bound a b x y))
    (AffineRankCoin.distSpec E p pcoin hpcoin (a * y) (b * y) (total a b x y)
      (total_pos a b x y hb hy) (right_bound a b x y))
  simp only [AffineRankCoin.callback, AffineRankCoin.body, total] at hrace
  iapply hrace.spec F (measurable_of_countable F) $$ Hcredit

/-- Full nonnegative rational offsets, positive denominators, and positive total exit mass. -/
theorem offsetRace_distSpec (E : CoPset) (p q : unitInterval) (a b x y : ℕ)
    (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ))
    (pcoin qcoin : Val rT)
    (hpcoin : IsDistSpec (GF := GF) E pl(&pcoin.fst #()) (RealCoin.law p) Val.bool)
    (hqcoin : IsDistSpec (GF := GF) E pl(&qcoin.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.offsetRace &pcoin.fst &qcoin.fst
      #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
      (RealCoin.law (bias p q a b x y hb hy)) Val.bool where
  spec F _ := wand_entails (twp_offsetRace E p q a b x y hb hy h pcoin qcoin hpcoin hqcoin F)

end specification

end

end SampLib.OffsetRace
