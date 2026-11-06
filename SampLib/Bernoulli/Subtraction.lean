import SampLib.Bernoulli.Laws.Subtraction
import SampLib.Bernoulli.Addition
import SampLib.Common.CoinComplement

/-! # Subtraction by complement and addition

The construction complements a coin of bias `(1-p)+q`, deriving bias `p-q`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Subtraction

noncomputable section

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.subtraction, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.subtraction := rfl

private theorem bool_not (b : Bool) : Bool.rec true false b = !b := by cases b <;> rfl

theorem subtraction_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.FactoryExtra.subtraction = Occil.FactoryExtra.subtraction :=
  (Exp.open_lc k e _ (by is_lc)).symm

theorem subtraction_fv {rT : Type} : (Occil.FactoryExtra.subtraction : Exp rT).fv = ∅ := by
  simp [Occil.FactoryExtra.subtraction, Exp.fv, Addition.addition_closeRec, Addition.addition_fv]

theorem subtraction_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.FactoryExtra.subtraction : Exp rT) = Occil.FactoryExtra.subtraction :=
  Exp.closeRec_fresh x _ k (by simp [subtraction_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable [ProbLangDist.IsUniformInt rT]
local bi (IProp GF)

/-- Derived subtraction law over the complete positive-margin domain. -/
theorem subtraction_distSpec (E : CoPset) (p q : unitInterval) (e f : ℤ)
    (he : 0 < e) (hef : e < f) (h : (e : ℝ) / f ≤ (p : ℝ) - q)
    (left right : Val rT)
    (hleft : IsDistSpec (GF := GF) E pl(&left.fst #()) (RealCoin.law p) Val.bool)
    (hright : IsDistSpec (GF := GF) E pl(&right.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.subtraction &left.fst &right.fst #int e #int f #())
      (RealCoin.law (bias p q e f he hef h)) Val.bool where
  spec F _ := by
    have hs := Addition.addition_distSpec (rT := rT) (GF := GF) E (unitInterval.symm p) q e f
      he hef (complement_bound p q e f h) (CoinComplement.callback left) right
      (CoinComplement.distSpec E p left hleft) hright
    iintro Hcredit
    rw [← source_fst (rT := rT)]
    iterate 5 (twp_step; simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Exp.ofVal,
      Var.internal.injEq, ProbLang.openRec_val_fst,
      Addition.addition_openRec, Addition.addition_closeRec])
    twp_bind pl(&Occil.FactoryExtra.addition &(CoinComplement.callback left).fst &right.fst
      #int e #int f #())
    isimp only [← expectation p q e f he hef h F] at Hcredit
    iapply (hs.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !b
    iframe Hcredit
    ipureintro
    simp only [Val.ext_iff, bool_not]

end specification

end

end SampLib.Subtraction
