import SampLib.Latent.UniformBagBracket
import SampLib.Core.BetaStep
import Samplers.General.Core

/-! # Shared source template for dyadic refinement

Only the bounds lookup differs between a fresh coin and a cached CDF comparison.
The recursive body is identified before callbacks are inserted.
-/

open ProbLang

namespace SampLib.RefinedComparison.Program

/-- The source's two-argument refinement loop, with a shared bag at every comparison. -/
def loopCode {rT : Type} (lookup : Exp rT) (bag : ℕ → Exp rT) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (bag 6)) x) (.bvar 3)
  let recur := .app (.app (.bvar 5) (.binop .plus (.bvar 4) (.lit (.int 1))))
    (.binop .mult (.bvar 3) (.lit (.int 2)))
  let invalid := .binop .or
    (.binop .or (.binop .lt (.bvar 1) (.lit (.int 0)))
      (.binop .lt (.bvar 0) (.bvar 1)))
    (.binop .lt (.bvar 3) (.bvar 0))
  let branch := .cond invalid .fail
    (.cond (compare (.bvar 1)) (.lit (.bool true))
      (.cond (compare (.bvar 0)) recur (.lit (.bool false))))
  let read := bind (.app lookup (.bvar 1))
    (bind (.fst (.bvar 0)) (bind (.snd (.bvar 1)) branch))
  .fix (.lam (.lam read))

def loop {rT : Type} (lookup : Exp rT) (l : Loc) : Exp rT :=
  loopCode lookup (fun _ => .lit (.loc l))

/-- One round retains the named recursive function as a locally closed leaf. -/
def round {rT : Type} (lookup recur : Exp rT) (l : Loc) (level denominator : ℤ) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (.lit (.loc l))) x) (.lit (.int denominator))
  let retry := .app (.app recur (.binop .plus (.lit (.int level)) (.lit (.int 1))))
    (.binop .mult (.lit (.int denominator)) (.lit (.int 2)))
  let invalid := .binop .or
    (.binop .or (.binop .lt (.bvar 1) (.lit (.int 0)))
      (.binop .lt (.bvar 0) (.bvar 1)))
    (.binop .lt (.lit (.int denominator)) (.bvar 0))
  let branch := .cond invalid .fail
    (.cond (compare (.bvar 1)) (.lit (.bool true))
      (.cond (compare (.bvar 0)) retry (.lit (.bool false))))
  bind (.app lookup (.lit (.int level)))
    (bind (.fst (.bvar 0)) (bind (.snd (.bvar 1)) branch))

theorem loop_lc {rT : Type} (lookup : Exp rT) (l : Loc)
    (hlookup : lookup.IsLocallyClosed) : (loop lookup l).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hl (k : ℕ) : Exp.lcb k lookup = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb hlookup) (Nat.zero_le k)
  have hu (k : ℕ) : Exp.lcb k (Occil.uniformBagLess : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb UniformBag.uniformBagLess_lc) (Nat.zero_le k)
  simp [loop, loopCode, Exp.lcb, hl, hu]

theorem loop_openRec {rT : Type} (lookup : Exp rT) (l : Loc)
    (hlookup : lookup.IsLocallyClosed) (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (loop lookup l) = loop lookup l :=
  (Exp.open_lc k e _ (loop_lc lookup l hlookup)).symm

/-- A checked closure certificate keeps recursive syntax opaque during pure steps. -/
@[irreducible] def loopValue {rT : Type} (lookup : Exp rT) (l : Loc)
    (hlookup : lookup.IsLocallyClosed) : Val rT :=
  ⟨loop lookup l, by exact IsVal.fix (loop_lc lookup l hlookup), loop_lc lookup l hlookup⟩

theorem loopValue_fst {rT : Type} (lookup : Exp rT) (l : Loc)
    (hlookup : lookup.IsLocallyClosed) : (loopValue lookup l hlookup).fst = loop lookup l := by
  unfold loopValue
  rfl

private def start {rT : Type} : Exp rT :=
  .app (.app (.bvar 0) (.lit (.int 1))) (.lit (.int 2))

/-- Source with a fresh cache. -/
def coinSource {rT : Type} : Exp rT :=
  .lam (.lam (.app (.lam (.app (.lam start)
    (loopCode (.bvar 5) (fun depth => .bvar depth))))
    (.app Occil.newUniformBag (.lit .unit))))

/-- Source with a supplied cache and an indexed bounds lookup. -/
def comparisonSource {rT : Type} : Exp rT :=
  .lam (.lam (.lam (.app (.lam start)
    (loopCode (.app (.bvar 4) (.bvar 3)) (fun depth => .bvar (depth + 2))))))

theorem coin_source_eq {rT : Type} :
    (Occil.General.refinedCoin : Exp rT) = coinSource := by
  kernel_rfl

theorem comparison_source_eq {rT : Type} :
    (Occil.General.refinedCDFComparison : Exp rT) = comparisonSource := by
  kernel_rfl

def coinBody {rT : Type} : Exp rT :=
  .lam (.app (.lam (.app (.lam start)
    (loopCode (.bvar 5) (fun depth => .bvar depth))))
    (.app Occil.newUniformBag (.lit .unit)))

theorem coin_source_lc {rT : Type} : (coinSource : Exp rT).IsLocallyClosed := by
  rw [← coin_source_eq]
  is_lc

theorem coin_unit_lc {rT : Type} (bounds : Val rT) :
    (Exp.open' coinBody bounds.fst).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb bounds.lc)
  change Exp.lcb 0 (coinSource : Exp rT) = true
  exact Exp.lc_imp_lcb coin_source_lc

def coinBagBody {rT : Type} (bounds : Val rT) : Exp rT :=
  .app (.lam start) (loopCode bounds.fst (fun depth => .bvar depth))

theorem inserted_coin_callback {rT : Type} (bounds : Val rT) :
    Exp.openRec 1 pl(#()) (Exp.openRec 2 bounds.fst
      (loopCode (.bvar 5) (fun depth => .bvar depth))) =
      loopCode bounds.fst (fun depth => .bvar depth) := by
  simp [loopCode, Exp.openRec, UniformBag.uniformBagLess_openRec,
    (Exp.open_lc 4 pl(#()) bounds.fst bounds.lc).symm]

theorem opened_coin_bag {rT : Type} (bounds : Val rT) (l : Loc) :
    Exp.open' (coinBagBody bounds) (Val.loc l).fst =
      pl(let decide := &(loop bounds.fst l); decide #1 #2) := by
  simp [coinBagBody, loop, loopCode, start, Exp.open', Exp.openRec,
    UniformBag.uniformBagLess_openRec,
    (Exp.open_lc 3 (Val.loc l).fst bounds.fst bounds.lc).symm]

theorem coin_bag_lc {rT : Type} (bounds : Val rT) :
    (Exp.lam (coinBagBody bounds)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hb (k : ℕ) : Exp.lcb k bounds.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb bounds.lc) (Nat.zero_le k)
  have hu (k : ℕ) : Exp.lcb k (Occil.uniformBagLess : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb UniformBag.uniformBagLess_lc) (Nat.zero_le k)
  simp [coinBagBody, loopCode, start, Exp.lcb, hb, hu]

def comparisonBody {rT : Type} : Exp rT :=
  .lam (.lam (.app (.lam start)
    (loopCode (.app (.bvar 4) (.bvar 3)) (fun depth => .bvar (depth + 2)))))

def comparisonBoundsBody {rT : Type} (l : Loc) : Exp rT :=
  .lam (.app (.lam start)
    (loopCode (.app (.bvar 4) (.bvar 3)) (fun _ => .lit (.loc l))))

def comparisonIndexBody {rT : Type} (bounds : Val rT) (l : Loc) : Exp rT :=
  .app (.lam start) (loopCode (.app bounds.fst (.bvar 3)) (fun _ => .lit (.loc l)))

theorem comparison_source_lc {rT : Type} :
    (comparisonSource : Exp rT).IsLocallyClosed := by
  rw [← comparison_source_eq]
  is_lc

theorem comparison_open_bag {rT : Type} (l : Loc) :
    Exp.open' (comparisonBody : Exp rT) (Val.loc l).fst =
      .lam (comparisonBoundsBody l) := by
  simp [comparisonBody, comparisonBoundsBody, loopCode, start, Exp.open', Exp.openRec,
    UniformBag.uniformBagLess_openRec]

theorem comparison_bounds_lc {rT : Type} (l : Loc) :
    (Exp.lam (comparisonBoundsBody l) : Exp rT).IsLocallyClosed := by
  rw [← comparison_open_bag]
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb (Val.loc l).lc)
  change Exp.lcb 0 (comparisonSource : Exp rT) = true
  exact Exp.lc_imp_lcb comparison_source_lc

theorem comparison_open_bounds {rT : Type} (bounds : Val rT) (l : Loc) :
    Exp.open' (comparisonBoundsBody l) bounds.fst = .lam (comparisonIndexBody bounds l) := by
  simp [comparisonBoundsBody, comparisonIndexBody, loopCode, start, Exp.open', Exp.openRec,
    UniformBag.uniformBagLess_openRec]

theorem comparison_index_lc {rT : Type} (bounds : Val rT) (l : Loc) :
    (Exp.lam (comparisonIndexBody bounds l)).IsLocallyClosed := by
  rw [← comparison_open_bounds]
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb bounds.lc)
  change Exp.lcb 0 (Exp.lam (comparisonBoundsBody l)) = true
  exact Exp.lc_imp_lcb (comparison_bounds_lc l)

theorem comparison_open_index {rT : Type} [ProbLangℝ rT] (bounds : Val rT) (l : Loc)
    (index : ℤ) :
    Exp.open' (comparisonIndexBody bounds l) (Val.int index).fst =
      pl(let decide := &(loop pl(&bounds.fst #int index) l); decide #1 #2) := by
  simp [comparisonIndexBody, loop, loopCode, start, Exp.open', Exp.openRec,
    UniformBag.uniformBagLess_openRec,
    (Exp.open_lc 3 (Val.int index).fst bounds.fst bounds.lc).symm]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open the two source arguments, retaining the fresh-bag allocation as the next action. -/
theorem twp_open_coin (E : CoPset) (bounds : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (coinBagBody bounds)) pl(&Occil.newUniformBag #())) Φ ⊢
      tglWp E pl(&Occil.General.refinedCoin &bounds.fst #()) Φ := by
  iintro H
  rw [coin_source_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL Val.unit]
      (.app (.lam coinBody) bounds.fst)) _)
  iapply (twp_beta E [.appL Val.unit] coinBody bounds
    coin_source_lc _)
  ieval (change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam _) Val.unit.fst)) _)
  iapply (twp_beta E [] _ Val.unit (coin_unit_lc bounds) _)
  simp only [Exp.open', Exp.openRec, Occil.newUniformBag,
    Nat.reduceAdd]
  rw [inserted_coin_callback]
  ieval (
    change _ ⊢ tglWp E (.app (.lam (coinBagBody bounds)) pl(&Occil.newUniformBag #())) Φ)
  isimp only [Occil.newUniformBag]
  iexact H

/-- Substitute the allocated bag and start the same recursive comparison loop. -/
theorem twp_open_coin_bag (E : CoPset) (bounds : Val rT) (l : Loc)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(loop bounds.fst l) #1 #2) Φ ⊢
      tglWp E (.app (.lam (coinBagBody bounds)) (Exp.ofVal (Val.loc l))) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill []
      (.app (.lam (coinBagBody bounds)) (Val.loc l).fst)) _)
  iapply (twp_beta E [] (coinBagBody bounds) (Val.loc l)
    (coin_bag_lc bounds) _)
  ieval (
    change _ ⊢ tglWp E
      ((coinBagBody bounds).open' (Val.loc l).fst) _)
  rw [opened_coin_bag]
  rw [← loopValue_fst bounds.fst l bounds.lc]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam pl(⟪bvar 0⟫ #1 #2))
      (loopValue bounds.fst l bounds.lc).fst)) _)
  iapply (twp_beta E [] pl(⟪bvar 0⟫ #1 #2)
    (loopValue bounds.fst l bounds.lc) (by is_lc) _)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec,
    loopValue_fst, ↓reduceIte]
  iexact H

/-- Open the cached, indexed comparison without normalizing its recursive body. -/
theorem twp_open_comparison (E : CoPset) (bounds : Val rT) (l : Loc) (index : ℤ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(loop pl(&bounds.fst #int index) l) #1 #2) Φ ⊢
      tglWp E pl(&Occil.General.refinedCDFComparison #loc l &bounds.fst #int index) Φ := by
  iintro H
  rw [comparison_source_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL bounds, .appL (Val.int index)]
      (.app (.lam comparisonBody) (Val.loc l).fst)) _)
  iapply (twp_beta E [.appL bounds, .appL (Val.int index)]
    comparisonBody (Val.loc l)
    comparison_source_lc _)
  rw [comparison_open_bag]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL (Val.int index)]
      (.app (.lam (comparisonBoundsBody l)) bounds.fst)) _)
  iapply (twp_beta E [.appL (Val.int index)]
    (comparisonBoundsBody l) bounds
    (comparison_bounds_lc l) _)
  rw [comparison_open_bounds]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill []
      (.app (.lam (comparisonIndexBody bounds l))
        (Val.int index).fst)) _)
  iapply (twp_beta E [] (comparisonIndexBody bounds l)
    (Val.int index) (comparison_index_lc bounds l) _)
  rw [comparison_open_index]
  have hlookup : pl(&bounds.fst #int index).IsLocallyClosed := by is_lc
  rw [← loopValue_fst pl(&bounds.fst #int index) l hlookup]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam pl(⟪bvar 0⟫ #1 #2))
      (loopValue pl(&bounds.fst #int index) l hlookup).fst)) _)
  iapply (twp_beta E [] pl(⟪bvar 0⟫ #1 #2)
    (loopValue pl(&bounds.fst #int index) l hlookup) (by is_lc) _)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec, loopValue_fst, ↓reduceIte]
  iexact H

end specification

end SampLib.RefinedComparison.Program
