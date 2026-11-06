import SampLib.PSRN.Syntax.PSRNExponentialWrappers
import SampLib.PSRN.Syntax.PSRNCoordinateSum
import SampLib.PSRN.Support.LatentDivideCoordinates
import SampLib.Core.GeneralSyntax

/-! # Source opening for the exponential construction of a simplex vector -/

open ProbLang

namespace SampLib.PSRNSimplex.Program

open scoped SampLib.LatentReal.CoordinateSum SampLib.PSRNExponential.Wrappers

private instance exponential_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newExponential : Exp rT) where
  lc := by
    rw [PSRNExponential.Wrappers.rational_source_eq]
    exact CurriedStep.lambdas_lc 3 _ (PSRNExponential.Wrappers.rational_lcb (rT := rT))
  fv := by kernel_rfl

theorem exponential_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.PSRN.newExponential = Occil.PSRN.newExponential :=
  (Exp.open_lc k e _ (exponential_closed (rT := rT)).lc).symm

private instance repeat_closed {rT : Type} : ClosedExp (Occil.repeatSample : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.repeatSample, Exp.fv]

private instance divide_coordinates_closed {rT : Type} :
    ClosedExp (Occil.PSRN.divideCoordinates : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

@[pl_fold] def sample {rT : Type} : Exp rT := pl% fun u,
  &Occil.PSRN.newExponential #1 #1 #()

private instance sample_closed {rT : Type} : ClosedExp (sample : Exp rT) where
  lc := by
    have h (k : ℕ) : Exp.lcb k (Occil.PSRN.newExponential : Exp rT) = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb (exponential_closed (rT := rT)).lc) (Nat.zero_le k)
    apply Exp.lcb_imp_lc
    simp [sample, Exp.close, Exp.closeRec, ClosedExp.closeRec, Exp.lcb, h]
  fv := by simp [sample, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

def sampleValue {rT : Type} : Val rT :=
  ⟨sample, by unfold sample; constructor; is_lc, (sample_closed (rT := rT)).lc⟩

theorem sample_fst {rT : Type} : (sampleValue (rT := rT)).fst =
    .lam pl(&Occil.PSRN.newExponential #1 #1 #()) := by
  simp [sampleValue, sample, Exp.close, Exp.closeRec, ClosedExp.closeRec]

@[pl_fold] def source {rT : Type} : Exp rT := pl%
  fun components u,
    if components <= #0 then fail else
    if components = #1 then inr((&Occil.PSRN.rational #1 #1, inl(#()))) else
      let coordinates := &Occil.repeatSample &sample components;
      let sum := &LatentReal.CoordinateSum.source;
      &Occil.PSRN.divideCoordinates coordinates (sum coordinates)

theorem source_eq {rT : Type} : (Occil.PSRN.newSimplex : Exp rT) = source := by
  simp [Occil.PSRN.newSimplex, source, sample, LatentReal.CoordinateSum.source,
    Exp.close, Exp.closeRec, ClosedExp.closeRec, Var.internal.injEq]

def body {rT : Type} : Exp rT :=
  match (source : Exp rT) with
  | .lam (.lam result) => result
  | _ => .fail

theorem source_lambdas {rT : Type} : (source : Exp rT) = CurriedStep.lambdas 2 body := by rfl

theorem body_lcb {rT : Type} : Exp.lcb 2 (body : Exp rT) = true := by
  have hr (k : ℕ) : Exp.lcb k (Occil.repeatSample : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (repeat_closed (rT := rT)).lc) (Nat.zero_le k)
  have hs (k : ℕ) : Exp.lcb k (sample : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (sample_closed (rT := rT)).lc) (Nat.zero_le k)
  have hd (k : ℕ) : Exp.lcb k (Occil.PSRN.divideCoordinates : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (divide_coordinates_closed (rT := rT)).lc) (Nat.zero_le k)
  have hq (k : ℕ) : Exp.lcb k (Occil.PSRN.rational : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (LatentReal.CoordinateSum.rational_closed (rT := rT)).lc)
      (Nat.zero_le k)
  have ht (k : ℕ) : Exp.lcb k (LatentReal.CoordinateSum.source : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb (LatentReal.CoordinateSum.sum_closed (rT := rT)).lc)
      (Nat.zero_le k)
  simp [body, source, Exp.close, Exp.closeRec, ClosedExp.closeRec, Exp.lcb, hr, hs, hd, hq, ht]

@[pl_fold] def openedBody {rT : Type} (components : ℤ) : Exp rT := pl(
  if #components <= #0 then fail else
  if #components = #1 then inr((&Occil.PSRN.rational #1 #1, inl(#()))) else
    let coordinates := &Occil.repeatSample &sample #components;
    let sum := &LatentReal.CoordinateSum.source;
    &Occil.PSRN.divideCoordinates coordinates (sum coordinates))

theorem opened_body {rT : Type} (components : ℤ) :
    CurriedStep.opened [.int components, .unit] body =
      (openedBody (rT := rT) components) := by
  simp [CurriedStep.opened, body, source, openedBody, Exp.openRec, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, ClosedExp.openRec, Var.internal.injEq]

end SampLib.PSRNSimplex.Program
