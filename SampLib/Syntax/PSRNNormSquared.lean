import SampLib.Syntax.ClosedExp
import Samplers.PSRN.Geometry

/-! # Closed source syntax for joint squared-norm construction -/

open ProbLang

namespace SampLib.LatentReal.NormSquared

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.rational, Exp.fv]

scoped instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.add, Exp.fv]

scoped instance multiply_closed {rT : Type} : ClosedExp (Occil.PSRN.multiply : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.multiply, Exp.fv]

scoped instance norm_closed {rT : Type} : ClosedExp (Occil.PSRN.normSquared : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.normSquared, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

def sourceCode {rT : Type} : Exp rT :=
  .fix (.lam (.case (.bvar 0)
    (.lam (.app (.app Occil.PSRN.rational (.lit (.int 0))) (.lit (.int 1))))
    (.lam (.app (.app Occil.PSRN.add
      (.app (.app Occil.PSRN.multiply (.fst (.bvar 0))) (.fst (.bvar 0))))
      (.app (.bvar 2) (.snd (.bvar 0)))))))

theorem source_eq_code {rT : Type} : (Occil.PSRN.normSquared : Exp rT) = sourceCode := by
  simp [Occil.PSRN.normSquared, sourceCode, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq]

def sourceBody {rT : Type} : Exp rT :=
  match (sourceCode : Exp rT) with
  | .fix body => body
  | _ => .lit .unit

def sourceValue {rT : Type} : Val rT := by
  have hc : (sourceCode : Exp rT).IsLocallyClosed := by
    rw [← source_eq_code]
    exact (norm_closed (rT := rT)).lc
  exact ⟨.fix sourceBody, .fix hc, hc⟩

theorem source_fst {rT : Type} : (sourceValue (rT := rT)).fst = Occil.PSRN.normSquared :=
  source_eq_code.symm

def nilBranch {rT : Type} : Val rT := by
  have hr (k : ℕ) : Exp.lcb k (Occil.PSRN.rational : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (rational_closed (rT := rT)).lc) (Nat.zero_le k)
  refine ⟨.lam (.app (.app Occil.PSRN.rational (.lit (.int 0))) (.lit (.int 1))),
    .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;> simp [Exp.lcb, hr]

def consBranchCode {rT : Type} : Exp rT :=
  .app (.app Occil.PSRN.add
    (.app (.app Occil.PSRN.multiply (.fst (.bvar 0))) (.fst (.bvar 0))))
    (.app (sourceValue (rT := rT)).fst (.snd (.bvar 0)))

def consBranch {rT : Type} : Val rT := by
  have ha (k : ℕ) : Exp.lcb k (Occil.PSRN.add : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (add_closed (rT := rT)).lc) (Nat.zero_le k)
  have hm (k : ℕ) : Exp.lcb k (Occil.PSRN.multiply : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (multiply_closed (rT := rT)).lc) (Nat.zero_le k)
  have hs (k : ℕ) : Exp.lcb k (sourceValue (rT := rT)).fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (sourceValue (rT := rT)).lc) (Nat.zero_le k)
  refine ⟨.lam consBranchCode, .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [consBranchCode, Exp.lcb, ha, hm, hs]

def openedBody {rT : Type} : Exp rT :=
  .case (.bvar 0) (nilBranch (rT := rT)).fst (consBranch (rT := rT)).fst

def openedValue {rT : Type} : Val rT := by
  have hn (k : ℕ) : Exp.lcb k (nilBranch (rT := rT)).fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (nilBranch (rT := rT)).lc) (Nat.zero_le k)
  have hc (k : ℕ) : Exp.lcb k (consBranch (rT := rT)).fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (consBranch (rT := rT)).lc) (Nat.zero_le k)
  refine ⟨.lam openedBody, .lam ?_, ?_⟩ <;> apply Exp.lcb_imp_lc <;>
    simp [openedBody, Exp.lcb, hn, hc]

theorem opened_source {rT : Type} :
    Exp.open' sourceBody (sourceValue (rT := rT)).fst = (openedValue (rT := rT)).fst := by
  simp [sourceBody, sourceCode, openedValue, openedBody, nilBranch, consBranch,
    consBranchCode, Exp.open', Exp.openRec, ClosedExp.openRec]

end SampLib.LatentReal.NormSquared
