import SampLib.Core.Syntax.ClosedExp
import SampLib.PSRN.Syntax.PSRNLess
import SampLib.Core.ListEncoding
import SampLib.PSRN.Support.PSRNLess
import Samplers.PSRN.Uniform

/-! # Closed recursive closures of the uniform order-statistic constructor -/

open ProbLang

namespace SampLib.PSRNOrderStatistic.Program

scoped instance less_closed {rT : Type} : ClosedExp (Occil.PSRN.less : Exp rT) where
  lc := LatentReal.Less.Program.source_eq (rT := rT) ▸ LatentReal.Less.Program.source_lc
  fv := by kernel_rfl

scoped instance uniform_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniform : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance getAt_closed {rT : Type} : ClosedExp (Occil.getAt : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

/-- The source's insertion closure. -/
@[pl_fold] def insert {rT : Type} : Exp rT := pl%
  rec put x xs := case! xs
    | inl(u) => inr((x, inl(#())))
    | inr(p) => if &Occil.PSRN.less x (fst(p)) then inr((x, xs)) else
      inr((fst(p), put x (snd(p))))

scoped instance insert_closed {rT : Type} : ClosedExp (insert : Exp rT) where
  lc := by
    have h (k : ℕ) : Exp.lcb k (Occil.PSRN.less : Exp rT) = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb (less_closed (rT := rT)).lc) (Nat.zero_le k)
    apply Exp.lcb_imp_lc
    simp [insert, Exp.close, Exp.closeRec, ClosedExp.closeRec, Exp.lcb, h]
  fv := by simp [insert, Exp.fv, Exp.close, Exp.closeRec, ClosedExp.closeRec, ClosedExp.fv]

/-- The source's construction closure, with the insertion closure substituted. -/
@[pl_fold] def build {rT : Type} : Exp rT := pl%
  rec draw remaining := if remaining = #0 then inl(#()) else
    let x := &Occil.PSRN.newUniform #();
    &insert x (draw (remaining - #1))

scoped instance build_closed {rT : Type} : ClosedExp (build : Exp rT) where
  lc := by
    have h (k : ℕ) : Exp.lcb k (Occil.PSRN.newUniform : Exp rT) = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb (uniform_closed (rT := rT)).lc) (Nat.zero_le k)
    have hi (k : ℕ) : Exp.lcb k (insert : Exp rT) = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb (insert_closed (rT := rT)).lc) (Nat.zero_le k)
    apply Exp.lcb_imp_lc
    simp [build, Exp.close, Exp.closeRec, ClosedExp.closeRec, Exp.lcb, h, hi]
  fv := by simp [build, Exp.fv, Exp.close, Exp.closeRec, ClosedExp.closeRec, ClosedExp.fv]

/-- The construction closure as it appears once the insertion closure is substituted. -/
theorem build_eq {rT : Type} :
    (.fix (.lam (.cond (.binop .eq (.bvar 0) (.lit (.int 0))) (.inl (.lit .unit))
      (.app (.lam (.app (.app insert (.bvar 0))
        (.app (.bvar 2) (.binop .minus (.bvar 1) (.lit (.int 1))))))
        (.app Occil.PSRN.newUniform (.lit .unit))))) : Exp rT) = build := by
  simp [build, Exp.close, Exp.closeRec, ClosedExp.closeRec, Var.internal.injEq]

/-- The source, with its two closures named. -/
@[pl_fold] def source {rT : Type} : Exp rT := pl%
  fun n k,
    if (n <= #0) || (k <= #0) || (n < k) then fail else
      let put := &insert;
      let draw := (rec draw remaining := if remaining = #0 then inl(#()) else
        let x := &Occil.PSRN.newUniform #();
        put x (draw (remaining - #1)));
      &Occil.getAt (draw n) (k - #1)

theorem source_eq {rT : Type} : (Occil.PSRN.newOrderStatistic : Exp rT) = source := by
  simp [Occil.PSRN.newOrderStatistic, source, insert, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- Inside the domain, the source reaches `getAt (build n) (k - 1)` deterministically. -/
theorem twp_open (E : CoPset) (n k : ℤ) (hk : 0 < k ∧ k ≤ n) (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.getAt (&build #n) (#k - #1)) Φ ⊢
      tglWp E pl(&Occil.PSRN.newOrderStatistic #n #k) Φ := by
  have hguard : ((decide (n ≤ 0)).or (decide (k ≤ 0))).or (decide (n < k)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le, not_lt]
    omega
  iintro H
  rw [source_eq]
  twp_pures
  rw [hguard]
  iterate 3 twp_pure
  rw [build_eq]
  iexact H

end specification

end SampLib.PSRNOrderStatistic.Program
