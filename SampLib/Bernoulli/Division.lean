import SampLib.Bernoulli.Subtraction
import SampLib.Bernoulli.BernoulliRace

/-! # Division by a Bernoulli race

Racing the numerator against the denominator-minus-numerator coin cancels their
common accepted mass. This derives division from the verified subtraction factory.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Division

noncomputable section

/-- The numerator's share of the two complementary accepted masses. -/
def bias (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) : unitInterval :=
  BernoulliRace.bias q (Subtraction.bias p q e f he hef h)

theorem bias_coe (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) : (bias p q e f he hef h : ℝ) = (q : ℝ) / p := by
  change (q : ℝ) / ((q : ℝ) + (Subtraction.bias p q e f he hef h : ℝ)) = _
  rw [Subtraction.bias_coe]
  congr 1
  ring

private theorem exit_pos (p q : unitInterval) (e f : ℤ) (he : 0 < e) (hef : e < f)
    (h : (e : ℝ) / f ≤ (p : ℝ) - q) :
    0 < (q : ℝ) + (Subtraction.bias p q e f he hef h : ℝ) := by
  have hg : 0 < (p : ℝ) - q :=
    lt_of_lt_of_le (div_pos (by exact_mod_cast he) (by exact_mod_cast he.trans hef)) h
  rw [Subtraction.bias_coe]
  linarith [q.2.1]

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.division, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.division := rfl

private def callback {rT : Type _} (denominator numerator : Val rT) (e f : ℤ) : Val rT :=
  ⟨.lam pl(&Occil.FactoryExtra.subtraction &denominator.fst &numerator.fst #int e #int f #()),
    .lam (by is_lc), by is_lc⟩

private theorem race_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.bernoulliRace = Occil.bernoulliRace :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem race_fv {rT : Type _} : (Occil.bernoulliRace : Exp rT).fv = ∅ := by
  simp [Occil.bernoulliRace, Exp.fv, FairCoin.fairCoin_fv]

private theorem race_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.bernoulliRace : Exp rT) = Occil.bernoulliRace :=
  Exp.closeRec_fresh x _ k (by simp [race_fv])

theorem division_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.division = Occil.FactoryExtra.division :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem division_fv {rT : Type} : (Occil.FactoryExtra.division : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.division, Exp.fv, Subtraction.subtraction_closeRec,
    Subtraction.subtraction_fv, race_closeRec, race_fv]

theorem division_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.division : Exp rT) = Occil.FactoryExtra.division :=
  Exp.closeRec_fresh x _ k (by simp [division_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable [ProbLangDist.IsUniformInt rT]
local bi (IProp GF)

private theorem callback_spec (E : CoPset) (p q : unitInterval) (e f : ℤ)
    (he : 0 < e) (hef : e < f) (h : (e : ℝ) / f ≤ (p : ℝ) - q)
    (denominator numerator : Val rT)
    (hden : IsDistSpec (GF := GF) E pl(&denominator.fst #()) (RealCoin.law p) Val.bool)
    (hnum : IsDistSpec (GF := GF) E pl(&numerator.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(callback denominator numerator e f).fst #())
      (RealCoin.law (Subtraction.bias p q e f he hef h)) Val.bool where
  spec F hF := by
    have hs := Subtraction.subtraction_distSpec (rT := rT) (GF := GF)
      E p q e f he hef h denominator numerator hden hnum
    iintro Hcredit
    twp_step
    simp [Exp.open', Exp.openRec, ProbLang.openRec_val_fst, Subtraction.subtraction_openRec]
    iapply hs.spec F hF $$ Hcredit

/-- Derived division law, including a zero numerator and the full supplied positive gap. -/
theorem division_distSpec (E : CoPset) (p q : unitInterval) (e f : ℤ)
    (he : 0 < e) (hef : e < f) (h : (e : ℝ) / f ≤ (p : ℝ) - q)
    (denominator numerator : Val rT)
    (hden : IsDistSpec (GF := GF) E pl(&denominator.fst #()) (RealCoin.law p) Val.bool)
    (hnum : IsDistSpec (GF := GF) E pl(&numerator.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.division &numerator.fst &denominator.fst #int e #int f #())
      (RealCoin.law (bias p q e f he hef h)) Val.bool where
  spec F hF := by
    have hr := BernoulliRace.bernoulliRace_distSpec (rT := rT) (GF := GF) E q
      (Subtraction.bias p q e f he hef h) (exit_pos p q e f he hef h)
      numerator (callback denominator numerator e f) hnum
      (callback_spec E p q e f he hef h denominator numerator hden hnum)
    simp only [callback] at hr
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 5 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst, race_openRec, race_closeRec,
      Subtraction.subtraction_openRec, Subtraction.subtraction_closeRec])
    isimp only [bias] at Hcredit
    iapply hr.spec F hF $$ Hcredit

end specification

end

end SampLib.Division
