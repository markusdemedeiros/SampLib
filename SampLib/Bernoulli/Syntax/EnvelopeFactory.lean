import SampLib.Bernoulli.Support.EnvelopeConditionalAverage
import SampLib.Bernoulli.Support.UniformBagChoice
import Samplers.Bernoulli.Series

/-! # Source interface for the adaptive Bernstein-envelope factory

Callbacks are inserted after closing the source binders. Named round and tail
expressions keep the CTE proof independent of de Bruijn bookkeeping.
-/

open ProbLang

namespace SampLib.EnvelopeFactory.Program

open FactoryFractions

private instance binomial_closed {rT : Type} : ClosedExp (Occil.binomial : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.binomial, Exp.fv]

private instance choose_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.choose : Exp rT) where
  lc := FactoryChoose.choose_lc
  fv := FactoryChoose.choose_fv

private instance multiply_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.multiplyFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.multiplyFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance divide_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.divideFraction : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.FactoryExtra.divideFraction, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private instance less_closed {rT : Type} : ClosedExp (Occil.uniformBagLess : Exp rT) where
  lc := UniformBag.uniformBagLess_lc
  fv := UniformBag.uniformBagLess_fv

private instance newBag_closed {rT : Type} : ClosedExp (Occil.newUniformBag : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.newUniformBag, Exp.fv]

/-- The two comparisons retain the same cached uniform and recurse on the new row. -/
def afterRescaleCode {rT : Type} (self bag degree heads lower upper : ℕ → Exp rT) : Exp rT :=
  let compare (threshold : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (bag 0)) (.fst threshold)) (.snd threshold)
  let retry := Exp.app (.app (.app (.app (self 0) (degree 0)) (heads 0)) (lower 0)) (upper 0)
  .cond (compare (lower 0)) pl(#true) (.cond (compare (upper 0)) retry pl(#false))

/-- Seven source lets perform the nine exact rational rescaling operations. -/
def afterConditionalCode {rT : Type}
    (self bag degree heads lo hi lower upper oldLower oldUpper : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let call (f a b : Exp rT) := .app (.app f a) b
  let remaining := call Occil.FactoryExtra.subtractFraction (hi 0) (lo 0)
  let width := call Occil.FactoryExtra.subtractFraction (oldUpper 1) (oldLower 1)
  let factor := call Occil.FactoryExtra.divideFraction (.bvar 1) (.bvar 0)
  let lowerGap := call Occil.FactoryExtra.subtractFraction (lower 3) (oldLower 3)
  let upperGap := call Occil.FactoryExtra.subtractFraction (oldUpper 4) (upper 4)
  let nextLower := call Occil.FactoryExtra.addFraction (lo 5)
    (call Occil.FactoryExtra.multiplyFraction (.bvar 1) (.bvar 2))
  let nextUpper := call Occil.FactoryExtra.subtractFraction (hi 6)
    (call Occil.FactoryExtra.multiplyFraction (.bvar 1) (.bvar 3))
  let finish := afterRescaleCode (fun d => self (d + 7)) (fun d => bag (d + 7))
    (fun d => degree (d + 7)) (fun d => heads (d + 7))
    (fun d => .bvar (d + 1)) Exp.bvar
  bind remaining (bind width (bind factor (bind lowerGap (bind upperGap
    (bind nextLower (bind nextUpper finish))))))

/-- One source round, before choosing the next degree. -/
def roundCode {rT : Type}
    (self coin bounds next bag n oldHeads lo hi : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let call (f a b : Exp rT) := .app (.app f a) b
  let degree := .app (next 0) (n 0)
  let heads := Exp.binop .plus (oldHeads 1)
    (call Occil.binomial (coin 1) (.binop .minus (.bvar 0) (n 1)))
  let current := call (bounds 2) (.bvar 1) (.bvar 0)
  let lower := Exp.fst (.bvar 0)
  let upper := Exp.snd (.bvar 1)
  let conditional := Exp.lam (EnvelopeConditionalAverage.bodyCode
    (fun d => bounds (d + 6)) (fun d => n (d + 6))
    (fun d => .bvar (d + 5)) (fun d => .bvar (d + 4)) Exp.bvar)
  let oldLower := Exp.app (.bvar 0) pl(#false)
  let oldUpper := Exp.app (.bvar 1) pl(#true)
  let rescale := afterConditionalCode (fun d => self (d + 8)) (fun d => bag (d + 8))
    (fun d => .bvar (d + 7)) (fun d => .bvar (d + 6))
    (fun d => lo (d + 8)) (fun d => hi (d + 8))
    (fun d => .bvar (d + 4)) (fun d => .bvar (d + 3))
    (fun d => .bvar (d + 1)) Exp.bvar
  bind degree (.cond (.binop .le (.bvar 0) (n 1)) .fail
    (bind heads (bind current (bind lower (bind upper
      (bind conditional (bind oldLower (bind oldUpper rescale))))))))

/-- Four arguments retain the previous degree, head count and uniform thresholds. -/
def loopCode {rT : Type} (coin bounds next bag : ℕ → Exp rT) : Exp rT :=
  .fix (.lam (.lam (.lam (.lam (roundCode
    (fun d => .bvar (d + 4)) (fun d => coin (d + 5)) (fun d => bounds (d + 5))
    (fun d => next (d + 5)) (fun d => bag (d + 5))
    (fun d => .bvar (d + 3)) (fun d => .bvar (d + 2))
    (fun d => .bvar (d + 1)) Exp.bvar)))))

def loop {rT : Type} (coin bounds next : Val rT) (l : Loc) : Exp rT :=
  loopCode (fun _ => coin.fst) (fun _ => bounds.fst) (fun _ => next.fst)
    (fun _ => (Val.loc l).fst)

def round {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ)
    (lo hi : Fraction) : Exp rT :=
  roundCode (fun _ => loop coin bounds next l) (fun _ => coin.fst) (fun _ => bounds.fst)
    (fun _ => next.fst) (fun _ => (Val.loc l).fst)
    (fun _ => pl(#int (n : ℤ))) (fun _ => pl(#int (heads : ℤ)))
    (fun _ => lo.encode.fst) (fun _ => hi.encode.fst)

def afterRescale {rT : Type} (self : Val rT) (l : Loc) (degree heads : ℕ)
    (lower upper : Fraction) : Exp rT :=
  afterRescaleCode (fun _ => self.fst) (fun _ => (Val.loc l).fst)
    (fun _ => pl(#int (degree : ℤ))) (fun _ => pl(#int (heads : ℤ)))
    (fun _ => lower.encode.fst) (fun _ => upper.encode.fst)

def afterConditional {rT : Type} (self : Val rT) (l : Loc) (degree heads : ℕ)
    (lo hi lower upper oldLower oldUpper : Fraction) : Exp rT :=
  afterConditionalCode (fun _ => self.fst) (fun _ => (Val.loc l).fst)
    (fun _ => pl(#int (degree : ℤ))) (fun _ => pl(#int (heads : ℤ)))
    (fun _ => lo.encode.fst) (fun _ => hi.encode.fst)
    (fun _ => lower.encode.fst) (fun _ => upper.encode.fst)
    (fun _ => oldLower.encode.fst) (fun _ => oldUpper.encode.fst)

def sourceCore {rT : Type} : Exp rT :=
  let initial := Exp.app (.app (.app (.app (.bvar 0) pl(#0)) pl(#0)) pl((#0, #1))) pl((#1, #1))
  .app (.lam (.app (.lam initial)
    (loopCode (fun d => .bvar (d + 4)) (fun d => .bvar (d + 3))
      (fun d => .bvar (d + 2)) Exp.bvar))) pl(&Occil.newUniformBag #())

def sourceBody {rT : Type} : Exp rT := .lam (.lam (.lam sourceCore))

def sourceCode {rT : Type} : Exp rT := .lam sourceBody

theorem source_eq {rT : Type} :
    (Occil.FactoryExtra.envelopeFactoryDegrees : Exp rT) = sourceCode := by
  simp [Occil.FactoryExtra.envelopeFactoryDegrees, sourceCode, sourceBody, sourceCore, loopCode,
    roundCode, afterConditionalCode, afterRescaleCode, EnvelopeConditionalAverage.bodyCode,
    EnvelopeConditionalAverage.loopCode, Exp.close, Exp.closeRec, Var.internal.injEq,
    ClosedExp.closeRec]
  rfl

theorem loop_lc {rT : Type} (coin bounds next : Val rT) (l : Loc) :
    (loop coin bounds next l).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hv (v : Val rT) (d : ℕ) : Exp.lcb d v.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb v.lc) (Nat.zero_le d)
  have hc (e : Exp rT) [ClosedExp e] (d : ℕ) : Exp.lcb d e = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb ClosedExp.lc) (Nat.zero_le d)
  simp [loop, loopCode, roundCode, afterConditionalCode, afterRescaleCode,
    EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode, Exp.lcb, hv, hc]
  rfl

def loopValue {rT : Type} (coin bounds next : Val rT) (l : Loc) : Val rT :=
  ⟨loop coin bounds next l, .fix (loop_lc coin bounds next l), loop_lc coin bounds next l⟩

@[simp] theorem loop_openRec {rT : Type} (coin bounds next : Val rT) (l : Loc)
    (d : ℕ) (e : Exp rT) :
    Exp.openRec d e (loop coin bounds next l) = loop coin bounds next l :=
  (Exp.open_lc d e _ (loop_lc coin bounds next l)).symm

def fixBody {rT : Type} (coin bounds next : Val rT) (l : Loc) : Exp rT :=
  match loop coin bounds next l with
  | .fix body => body
  | _ => .fail

private theorem loop_eq {rT : Type} (coin bounds next : Val rT) (l : Loc) :
    loop coin bounds next l = .fix (fixBody coin bounds next l) := rfl

def nBody {rT : Type} (coin bounds next : Val rT) (l : Loc) : Exp rT :=
  .lam (.lam (.lam (roundCode (fun _ => loop coin bounds next l)
    (fun _ => coin.fst) (fun _ => bounds.fst) (fun _ => next.fst)
    (fun _ => (Val.loc l).fst) (fun d => .bvar (d + 3)) (fun d => .bvar (d + 2))
    (fun d => .bvar (d + 1)) Exp.bvar)))

def headsBody {rT : Type} (coin bounds next : Val rT) (l : Loc) (n : ℕ) : Exp rT :=
  .lam (.lam (roundCode (fun _ => loop coin bounds next l)
    (fun _ => coin.fst) (fun _ => bounds.fst) (fun _ => next.fst)
    (fun _ => (Val.loc l).fst) (fun _ => pl(#int (n : ℤ)))
    (fun d => .bvar (d + 2)) (fun d => .bvar (d + 1)) Exp.bvar))

def lowerBody {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ) : Exp rT :=
  .lam (roundCode (fun _ => loop coin bounds next l)
    (fun _ => coin.fst) (fun _ => bounds.fst) (fun _ => next.fst)
    (fun _ => (Val.loc l).fst) (fun _ => pl(#int (n : ℤ)))
    (fun _ => pl(#int (heads : ℤ))) (fun d => .bvar (d + 1)) Exp.bvar)

def upperBody {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ)
    (lo : Fraction) : Exp rT :=
  roundCode (fun _ => loop coin bounds next l) (fun _ => coin.fst) (fun _ => bounds.fst)
    (fun _ => next.fst) (fun _ => (Val.loc l).fst)
    (fun _ => pl(#int (n : ℤ))) (fun _ => pl(#int (heads : ℤ)))
    (fun _ => lo.encode.fst) Exp.bvar

theorem opened_fix {rT : Type} (coin bounds next : Val rT) (l : Loc) :
    Exp.open' (fixBody coin bounds next l) (loop coin bounds next l) =
      .lam (nBody coin bounds next l) := by
  simp [fixBody, loop, loopCode, nBody, roundCode, afterConditionalCode, afterRescaleCode,
    EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]
  rfl

theorem opened_n {rT : Type} (coin bounds next : Val rT) (l : Loc) (n : ℕ) :
    Exp.open' (nBody coin bounds next l) (Val.int (n : ℤ)).fst =
      .lam (headsBody coin bounds next l n) := by
  simp [nBody, headsBody, roundCode, afterConditionalCode, afterRescaleCode,
    EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]
  rfl

theorem opened_heads {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ) :
    Exp.open' (headsBody coin bounds next l n) (Val.int (heads : ℤ)).fst =
      .lam (lowerBody coin bounds next l n heads) := by
  simp [headsBody, lowerBody, roundCode, afterConditionalCode, afterRescaleCode,
    EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]
  rfl

theorem opened_lower {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ)
    (lo : Fraction) :
    Exp.open' (lowerBody coin bounds next l n heads) lo.encode.fst =
      .lam (upperBody coin bounds next l n heads lo) := by
  simp [lowerBody, upperBody, roundCode, afterConditionalCode, afterRescaleCode,
    EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]
  rfl

theorem opened_upper {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ)
    (lo hi : Fraction) :
    Exp.open' (upperBody coin bounds next l n heads lo) hi.encode.fst =
      round coin bounds next l n heads lo hi := by
  simp [upperBody, round, roundCode, afterConditionalCode, afterRescaleCode,
    EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]
  rfl

theorem nBody_lc {rT : Type} (coin bounds next : Val rT) (l : Loc) :
    (Exp.lam (nBody coin bounds next l)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hbody : Exp.lcb 1 (fixBody coin bounds next l) = true := by
    change Exp.lcb 0 (loop coin bounds next l) = true
    exact Exp.lc_imp_lcb (loop_lc coin bounds next l)
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (loop_lc coin bounds next l)) hbody
  change Exp.lcb 0 (Exp.open' (fixBody coin bounds next l) (loop coin bounds next l)) = true at h
  rw [opened_fix] at h
  exact h

theorem headsBody_lc {rT : Type} (coin bounds next : Val rT) (l : Loc) (n : ℕ) :
    (Exp.lam (headsBody coin bounds next l n)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (Val.int (n : ℤ) : Val rT).lc)
    (Exp.lc_imp_lcb (nBody_lc coin bounds next l))
  change Exp.lcb 0 (Exp.open' (nBody coin bounds next l) (Val.int (n : ℤ)).fst) = true at h
  rw [opened_n] at h
  exact Exp.lcb_imp_lc h

theorem lowerBody_lc {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ) :
    (Exp.lam (lowerBody coin bounds next l n heads)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (Val.int (heads : ℤ) : Val rT).lc)
    (Exp.lc_imp_lcb (headsBody_lc coin bounds next l n))
  change Exp.lcb 0 (Exp.open' (headsBody coin bounds next l n)
    (Val.int (heads : ℤ)).fst) = true at h
  rw [opened_heads] at h
  exact Exp.lcb_imp_lc h

theorem upperBody_lc {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ)
    (lo : Fraction) : (Exp.lam (upperBody coin bounds next l n heads lo)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (lo.encode : Val rT).lc)
    (Exp.lc_imp_lcb (lowerBody_lc coin bounds next l n heads))
  change Exp.lcb 0 (Exp.open' (lowerBody coin bounds next l n heads) lo.encode.fst) = true at h
  rw [opened_lower] at h
  exact Exp.lcb_imp_lc h

/-- The actual recursive application at a rational threshold state. -/
def call {rT : Type} (coin bounds next : Val rT) (l : Loc) (n heads : ℕ)
    (lo hi : Fraction) : Exp rT :=
  .app (.app (.app (.app (loop coin bounds next l) pl(#int (n : ℤ)))
    pl(#int (heads : ℤ))) lo.encode.fst) hi.encode.fst

def boundsBody {rT : Type} (coin : Val rT) : Exp rT :=
  .lam (.lam (Exp.openRec 3 coin.fst sourceCore))

def nextBody {rT : Type} (coin bounds : Val rT) : Exp rT :=
  .lam (Exp.openRec 2 bounds.fst (Exp.openRec 3 coin.fst sourceCore))

def unitBody {rT : Type} (coin bounds next : Val rT) : Exp rT :=
  Exp.openRec 1 next.fst (Exp.openRec 2 bounds.fst (Exp.openRec 3 coin.fst sourceCore))

def initialCall {rT : Type} : Exp rT :=
  .app (.app (.app (.app (.bvar 0) pl(#0)) pl(#0)) pl((#0, #1))) pl((#1, #1))

def bagBody {rT : Type} (coin bounds next : Val rT) : Exp rT :=
  .app (.lam initialCall) (loopCode (fun _ => coin.fst) (fun _ => bounds.fst)
    (fun _ => next.fst) Exp.bvar)

def initialization {rT : Type} (coin bounds next : Val rT) : Exp rT :=
  .app (.lam (bagBody coin bounds next)) pl(&Occil.newUniformBag #())

theorem source_lc {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

private theorem open_lam_lc {rT : Type} (body : Exp rT) (v : Val rT)
    (h : (Exp.lam body).IsLocallyClosed) : (Exp.open' body v.fst).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (k := 0) (e := body) (Exp.lc_imp_lcb v.lc)
  exact Exp.lc_imp_lcb h

theorem boundsBody_lc {rT : Type} (coin : Val rT) :
    (Exp.lam (boundsBody coin)).IsLocallyClosed :=
  open_lam_lc sourceBody coin source_lc

theorem nextBody_lc {rT : Type} (coin bounds : Val rT) :
    (Exp.lam (nextBody coin bounds)).IsLocallyClosed :=
  open_lam_lc (boundsBody coin) bounds (boundsBody_lc coin)

theorem unitBody_lc {rT : Type} (coin bounds next : Val rT) :
    (Exp.lam (unitBody coin bounds next)).IsLocallyClosed :=
  open_lam_lc (nextBody coin bounds) next (nextBody_lc coin bounds)

theorem opened_unit {rT : Type} (coin bounds next : Val rT) :
    Exp.open' (unitBody coin bounds next) (Val.unit : Val rT).fst =
      initialization coin bounds next := by
  simp [unitBody, sourceCore, initialization, bagBody, initialCall, loopCode, roundCode,
    afterConditionalCode, afterRescaleCode, EnvelopeConditionalAverage.bodyCode,
    EnvelopeConditionalAverage.loopCode, Exp.open', Exp.openRec, openRec_val_fst,
    ClosedExp.openRec]
  rfl

theorem bagBody_lc {rT : Type} (coin bounds next : Val rT) :
    (Exp.lam (bagBody coin bounds next)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (Val.unit : Val rT).lc)
    (Exp.lc_imp_lcb (unitBody_lc coin bounds next))
  change Exp.lcb 0 (Exp.open' (unitBody coin bounds next) Val.unit.fst) = true at h
  rw [opened_unit] at h
  exact Exp.lcb_imp_lc (Bool.and_eq_true_iff.mp h).1

theorem opened_bag {rT : Type} (coin bounds next : Val rT) (l : Loc) :
    Exp.open' (bagBody coin bounds next) (Val.loc l).fst =
      .app (.lam initialCall) (loop coin bounds next l) := by
  simp [bagBody, loop, loopCode, initialCall, roundCode, afterConditionalCode,
    afterRescaleCode, EnvelopeConditionalAverage.bodyCode, EnvelopeConditionalAverage.loopCode,
    Exp.open', Exp.openRec, openRec_val_fst, ClosedExp.openRec]
  rfl

end SampLib.EnvelopeFactory.Program
