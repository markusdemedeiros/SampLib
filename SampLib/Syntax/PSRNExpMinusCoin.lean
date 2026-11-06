import SampLib.CurriedStep
import SampLib.Syntax.ClosedExp
import Samplers.PSRN.Exponential

/-! # Structural opening of the conditional PSRN exponential trial -/

open ProbLang

namespace SampLib.LatentReal.ExpMinusCoin.Program

scoped instance floor_closed {rT : Type} : ClosedExp (Occil.PSRN.floorScaled : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance subtract_closed {rT : Type} : ClosedExp (Occil.PSRN.subtract : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance exponentialRational_closed {rT : Type} :
    ClosedExp (Occil.expMinusRational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance exponential_closed {rT : Type} : ClosedExp (Occil.expMinusFactory : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance coin_closed {rT : Type} : ClosedExp (Occil.PSRN.coin : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance source_closed {rT : Type} : ClosedExp (Occil.PSRN.expMinusCoin : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.LatentReal.ExpMinusCoin.Program

def callback {rT : Type} (source : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.PSRN.expMinusCoin &source.fst #()), .lam (by is_lc), by is_lc⟩

/-- The callback's binder is fixed before inserting the arbitrary source handle. -/
def fractionCoin {rT : Type} (fraction : Val rT) : Val rT :=
  ⟨.lam pl(&Occil.PSRN.coin &fraction.fst #()), .lam (by is_lc), by is_lc⟩

def afterFraction {rT : Type} (z : ℤ) : Exp rT :=
  let callback := Exp.lam pl(&Occil.PSRN.coin {Exp.bvar 1} #())
  pl(if &Occil.expMinusRational #int z #1 #() then
    &Occil.expMinusFactory &callback #() else #false)

def afterWhole {rT : Type} (source : Val rT) : Exp rT :=
  let fraction := pl(&Occil.PSRN.subtract &source.fst (&Occil.PSRN.rational {Exp.bvar 0} #1))
  let callback := Exp.lam pl(&Occil.PSRN.coin {Exp.bvar 1} #())
  let tail := pl(if &Occil.expMinusRational {Exp.bvar 1} #1 #() then
    &Occil.expMinusFactory &callback #() else #false)
  .cond pl({Exp.bvar 0} < #0) .fail (.app (.lam tail) fraction)

def fractionBody {rT : Type} (source : Val rT) (z : ℤ) : Exp rT :=
  .app (.lam (afterFraction z))
    pl(&Occil.PSRN.subtract &source.fst (&Occil.PSRN.rational #int z #1))

theorem opened_afterWhole {rT : Type} (source : Val rT) (z : ℤ) :
    Exp.open' (afterWhole source) (Val.int z).fst =
      .cond pl(#int z < #0) .fail (fractionBody source z) := by
  simp [Exp.open', afterWhole, afterFraction, fractionBody, Exp.openRec,
    ClosedExp.openRec, ProbLang.openRec_val_fst]

theorem opened_afterFraction {rT : Type} (fraction : Val rT) (z : ℤ) :
    Exp.open' (afterFraction z) fraction.fst =
      pl(if &Occil.expMinusRational #int z #1 #() then
        &Occil.expMinusFactory &(fractionCoin fraction).fst #() else #false) := by
  simp [Exp.open', afterFraction, fractionCoin, Exp.openRec, ClosedExp.openRec]

def body {rT : Type} (source : Val rT) : Exp rT :=
  .app (.lam (afterWhole source)) pl(&Occil.PSRN.floorScaled &source.fst #1)

def sourceBody {rT : Type} : Exp rT :=
  match (Occil.PSRN.expMinusCoin : Exp rT) with
  | .lam (.lam body) => body
  | _ => .fail

theorem source_eq {rT : Type} : (Occil.PSRN.expMinusCoin : Exp rT) =
    CurriedStep.lambdas 2 sourceBody := by kernel_rfl

theorem sourceBody_lcb {rT : Type} : Exp.lcb 2 (sourceBody : Exp rT) = true := by
  lcb_decide

set_option maxHeartbeats 800000 in
theorem opened_source {rT : Type} (source : Val rT) :
    CurriedStep.opened [source, .unit] sourceBody = body source := by
  simp [CurriedStep.opened, sourceBody, Occil.PSRN.expMinusCoin, body, afterWhole,
    Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.openRec, ClosedExp.closeRec, ProbLang.openRec_val_fst]

end SampLib.LatentReal.ExpMinusCoin.Program
