import SampLib.FactoryFractions
import SampLib.UniformBagChoice
import Samplers.Bernoulli.Series

/-! # Binder interface for the arbitrary alternating-series factory

The structural source identity is checked before callbacks are inserted. The
closed loop then preserves the free variables of arbitrary callback values.
-/

open ProbLang

namespace SampLib.AlternatingSeries.Program

/-- The four accumulator arguments are index, lower bound, upper bound and live weight. -/
def loopCode {rT : Type} (coin coefficient bag : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (bag 9)) (.fst x)) (.snd x)
  let retry := pl({Exp.bvar 8} ({Exp.bvar 7} + #1)
    {Exp.bvar 1} {Exp.bvar 0} {Exp.bvar 3})
  let branch := .cond (compare (.bvar 1)) pl(#true)
    (.cond (compare (.bvar 0)) retry pl(#false))
  let upper := .cond pl({Exp.bvar 6} % #2 = #0)
    pl(&Occil.FactoryExtra.addFraction {Exp.bvar 5} {Exp.bvar 1}) (.bvar 4)
  let lower := .cond pl({Exp.bvar 5} % #2 = #1)
    pl(&Occil.FactoryExtra.subtractFraction {Exp.bvar 3} {Exp.bvar 0}) (.bvar 4)
  let term := .cond (.bvar 0) (.app (coefficient 6) (.bvar 4)) pl((#0, #1))
  let next := .cond (.bvar 0) (.app (coin 5) pl(#())) pl(#false)
  .fix (.lam (.lam (.lam (.lam (bind next (bind term (bind lower (bind upper branch))))))))

def loop {rT : Type} (coin coefficient : Val rT) (l : Loc) : Exp rT :=
  loopCode (fun _ => coin.fst) (fun _ => coefficient.fst) (fun _ => pl(#loc l))

def sourceCore {rT : Type} : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let start := pl({Exp.bvar 0} #1 (#0, #1) {Exp.bvar 1} #true)
  let body := bind (loopCode (fun depth => .bvar (depth + 4))
    (fun depth => .bvar (depth + 3)) (fun depth => .bvar (depth + 1))) start
  bind pl(&Occil.newUniformBag #()) (bind (.app (.bvar 2) pl(#0)) body)

def sourceBody {rT : Type} : Exp rT := .lam (.lam sourceCore)

def sourceCode {rT : Type} : Exp rT := .lam sourceBody

def coefficientBody {rT : Type} (coin : Val rT) : Exp rT :=
  .lam (Exp.openRec 2 coin.fst sourceCore)

def unitBody {rT : Type} (coin coefficient : Val rT) : Exp rT :=
  Exp.openRec 1 coefficient.fst (Exp.openRec 2 coin.fst sourceCore)

def bagBody {rT : Type} (coin coefficient : Val rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let start := pl({Exp.bvar 0} #1 (#0, #1) {Exp.bvar 1} #true)
  bind (.app coefficient.fst pl(#0))
    (bind (loopCode (fun _ => coin.fst) (fun _ => coefficient.fst)
      (fun depth => .bvar (depth + 1))) start)

def initialBody {rT : Type} (coin coefficient : Val rT) (l : Loc) : Exp rT :=
  let start := pl({Exp.bvar 0} #1 (#0, #1) {Exp.bvar 1} #true)
  .app (.lam start) (loop coin coefficient l)

theorem source_eq {rT : Type} :
    (Occil.FactoryExtra.alternatingSeries : Exp rT) = sourceCode := by
  kernel_rfl

theorem loop_locallyClosed {rT : Type} (coin coefficient : Val rT) (l : Loc) :
    (loop coin coefficient l).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hv (v : Val rT) (k : ℕ) : Exp.lcb k v.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb v.lc) (Nat.zero_le k)
  have ha (k : ℕ) : Exp.lcb k (Occil.FactoryExtra.addFraction : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb FactoryFractions.addFraction_closed.lc) (Nat.zero_le k)
  have hs (k : ℕ) : Exp.lcb k (Occil.FactoryExtra.subtractFraction : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb FactoryFractions.subtractFraction_closed.lc) (Nat.zero_le k)
  have hu (k : ℕ) : Exp.lcb k (Occil.uniformBagLess : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb UniformBag.uniformBagLess_lc) (Nat.zero_le k)
  simp [loop, loopCode, Exp.lcb, hv, ha, hs, hu]

instance newUniformBag_closed {rT : Type} :
    ClosedExp (Occil.newUniformBag : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.newUniformBag, Exp.fv]

instance alternatingSeries_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.alternatingSeries : Exp rT) where
  lc := by is_lc
  fv := by
    rw [source_eq]
    simp [sourceCode, sourceBody, sourceCore, loopCode, Exp.fv, ClosedExp.fv,
      UniformBag.uniformBagLess_fv, Occil.newUniformBag]

theorem source_locallyClosed {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  exact ClosedExp.lc

theorem coefficient_locallyClosed {rT : Type} (coin : Val rT) :
    (Exp.lam (coefficientBody coin)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 0 (Exp.open' sourceBody coin.fst) = true
  apply Exp.lcb_openRec (Exp.lc_imp_lcb coin.lc)
  change Exp.lcb 0 (sourceCode : Exp rT) = true
  exact Exp.lc_imp_lcb source_locallyClosed

theorem unit_locallyClosed {rT : Type} (coin coefficient : Val rT) :
    (Exp.lam (unitBody coin coefficient)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  change Exp.lcb 0 (Exp.open' (coefficientBody coin) coefficient.fst) = true
  apply Exp.lcb_openRec (Exp.lc_imp_lcb coefficient.lc)
  change Exp.lcb 0 (Exp.lam (coefficientBody coin)) = true
  exact Exp.lc_imp_lcb (coefficient_locallyClosed coin)

theorem opened_unit {rT : Type} (coin coefficient : Val rT) :
    Exp.open' (unitBody coin coefficient) Val.unit.fst =
      .app (.lam (bagBody coin coefficient)) pl(&Occil.newUniformBag #()) := by
  simp [unitBody, sourceCore, bagBody, loopCode, Exp.open', Exp.openRec,
    ClosedExp.openRec, UniformBag.uniformBagLess_openRec, openRec_val_fst]

theorem bag_locallyClosed {rT : Type} (coin coefficient : Val rT) :
    (Exp.lam (bagBody coin coefficient)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (Val.unit : Val rT).lc)
    (Exp.lc_imp_lcb (unit_locallyClosed coin coefficient))
  change Exp.lcb 0 (Exp.open' (unitBody coin coefficient) Val.unit.fst) = true at h
  rw [opened_unit] at h
  exact Exp.lcb_imp_lc (Bool.and_eq_true_iff.mp h).1

theorem opened_bag {rT : Type} (coin coefficient : Val rT) (l : Loc) :
    Exp.open' (bagBody coin coefficient) (Val.loc l).fst =
      .app (.lam (initialBody coin coefficient l)) pl(&coefficient.fst #0) := by
  simp [bagBody, initialBody, loop, loopCode, Exp.open', Exp.openRec,
    ClosedExp.openRec, UniformBag.uniformBagLess_openRec, openRec_val_fst]

theorem initial_locallyClosed {rT : Type} (coin coefficient : Val rT) (l : Loc) :
    (Exp.lam (initialBody coin coefficient l)).IsLocallyClosed := by
  have h := Exp.lcb_openRec (Exp.lc_imp_lcb (Val.loc l : Val rT).lc)
    (Exp.lc_imp_lcb (bag_locallyClosed coin coefficient))
  change Exp.lcb 0 (Exp.open' (bagBody coin coefficient) (Val.loc l).fst) = true at h
  rw [opened_bag] at h
  exact Exp.lcb_imp_lc (Bool.and_eq_true_iff.mp h).1

theorem opened_initial {rT : Type} (coin coefficient initial : Val rT) (l : Loc) :
    Exp.open' (initialBody coin coefficient l) initial.fst =
      .app (.lam pl({Exp.bvar 0} #1 (#0, #1) &initial.fst #true))
        (loop coin coefficient l) := by
  have hl : Exp.openRec 0 initial.fst (loop coin coefficient l) = loop coin coefficient l :=
    (Exp.open_lc 0 initial.fst _ (loop_locallyClosed coin coefficient l)).symm
  simp [initialBody, Exp.open', Exp.openRec, hl]

end SampLib.AlternatingSeries.Program
