import SampLib.Syntax.RefinedComparison
import SampLib.BetaStep

/-! # Source template for finite inversion with a shared cached uniform -/

open ProbLang

namespace SampLib.IncompleteInformation.Program

/-- Bisection keeps one bag and one bounds oracle throughout its recursive calls. -/
def searchCode {rT : Type} (bounds : Exp rT) (bag : ℕ → Exp rT) : Exp rT :=
  let test := .app (.app (.app Occil.General.refinedCDFComparison (bag 4)) bounds) (.bvar 0)
  let left := .app (.app (.bvar 3) (.bvar 2)) (.bvar 0)
  let right := .app (.app (.bvar 3) (.binop .plus (.bvar 0) (.lit (.int 1)))) (.bvar 1)
  let midpoint := .binop .div (.binop .plus (.bvar 1) (.bvar 0)) (.lit (.int 2))
  .fix (.lam (.lam (.cond (.binop .eq (.bvar 1) (.bvar 0)) (.bvar 1)
    (.app (.lam (.cond test left right)) midpoint))))

def search {rT : Type} (bounds : Val rT) (l : Loc) : Exp rT :=
  searchCode bounds.fst (fun _ => .lit (.loc l))

/-- The complete source is identified before arbitrary bounds callbacks are inserted. -/
def sourceCode {rT : Type} : Exp rT :=
  let start := .app (.app (.bvar 0) (.lit (.int 0)))
    (.binop .minus (.bvar 4) (.lit (.int 1)))
  let decide := .app (.lam start) (searchCode (.bvar 6) (fun depth => .bvar depth))
  let allocate := .app (.lam decide) (.app Occil.newUniformBag (.lit .unit))
  .lam (.lam (.lam (.cond (.binop .le (.bvar 2) (.lit (.int 0))) .fail allocate)))

theorem source_eq {rT : Type} :
    (Occil.General.incompleteInformation : Exp rT) = sourceCode := by
  kernel_rfl

theorem comparison_lc {rT : Type} :
    (Occil.General.refinedCDFComparison : Exp rT).IsLocallyClosed := by is_lc

@[simp] theorem comparison_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.General.refinedCDFComparison = Occil.General.refinedCDFComparison :=
  (Exp.open_lc k e _ comparison_lc).symm

private def startCode {rT : Type} (size : Exp rT) : Exp rT :=
  .app (.app (.bvar 0) (.lit (.int 0))) (.binop .minus size (.lit (.int 1)))

def bagBody {rT : Type} (size : ℤ) (bounds : Val rT) : Exp rT :=
  .app (.lam (startCode (.lit (.int size))))
    (searchCode bounds.fst (fun depth => .bvar depth))

def unitBody {rT : Type} (size : ℤ) (bounds : Val rT) : Exp rT :=
  .cond (.binop .le (.lit (.int size)) (.lit (.int 0))) .fail
    (.app (.lam (bagBody size bounds)) (.app Occil.newUniformBag (.lit .unit)))

def boundsBody {rT : Type} (size : ℤ) : Exp rT :=
  let decide := .app (.lam (startCode (.lit (.int size))))
    (searchCode (.bvar 6) (fun depth => .bvar depth))
  .lam (.cond (.binop .le (.lit (.int size)) (.lit (.int 0))) .fail
    (.app (.lam decide) (.app Occil.newUniformBag (.lit .unit))))

def sourceBody {rT : Type} : Exp rT :=
  let decide := .app (.lam (startCode (.bvar 4)))
    (searchCode (.bvar 6) (fun depth => .bvar depth))
  .lam (.lam (.cond (.binop .le (.bvar 2) (.lit (.int 0))) .fail
    (.app (.lam decide) (.app Occil.newUniformBag (.lit .unit)))))

theorem source_lc {rT : Type} : (sourceCode : Exp rT).IsLocallyClosed := by
  rw [← source_eq]
  is_lc

theorem open_size {rT : Type} (size : ℤ) :
    Exp.open' (sourceBody : Exp rT) (Val.int size).fst = .lam (boundsBody size) := by
  simp [sourceBody, boundsBody, startCode, searchCode, Exp.open', Exp.openRec,
    comparison_openRec, Occil.newUniformBag]

theorem bounds_lc {rT : Type} (size : ℤ) :
    (Exp.lam (boundsBody size) : Exp rT).IsLocallyClosed := by
  rw [← open_size]
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb (Val.int size).lc)
  change Exp.lcb 0 (sourceCode : Exp rT) = true
  exact Exp.lc_imp_lcb source_lc

theorem open_bounds {rT : Type} (size : ℤ) (bounds : Val rT) :
    Exp.open' (boundsBody size) bounds.fst = .lam (unitBody size bounds) := by
  simp [boundsBody, unitBody, bagBody, startCode, searchCode, Exp.open', Exp.openRec,
    comparison_openRec, Occil.newUniformBag]

theorem unit_lc {rT : Type} (size : ℤ) (bounds : Val rT) :
    (Exp.lam (unitBody size bounds)).IsLocallyClosed := by
  rw [← open_bounds]
  apply Exp.lcb_imp_lc
  apply Exp.lcb_openRec (Exp.lc_imp_lcb bounds.lc)
  change Exp.lcb 0 (Exp.lam (boundsBody size)) = true
  exact Exp.lc_imp_lcb (bounds_lc size)

theorem open_unit {rT : Type} (size : ℤ) (bounds : Val rT) :
    Exp.open' (unitBody size bounds) (Val.unit).fst = unitBody size bounds := by
  simp [unitBody, bagBody, startCode, searchCode, Exp.open', Exp.openRec,
    comparison_openRec, Occil.newUniformBag,
    (Exp.open_lc 5 Val.unit.fst bounds.fst bounds.lc).symm]

theorem bag_lc {rT : Type} (size : ℤ) (bounds : Val rT) :
    (Exp.lam (bagBody size bounds)).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hb (k : ℕ) : Exp.lcb k bounds.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb bounds.lc) (Nat.zero_le k)
  have hc (k : ℕ) : Exp.lcb k (Occil.General.refinedCDFComparison : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb comparison_lc) (Nat.zero_le k)
  simp [bagBody, startCode, searchCode, Exp.lcb, hb, hc]

theorem search_lc {rT : Type} (bounds : Val rT) (l : Loc) :
    (search bounds l).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hb (k : ℕ) : Exp.lcb k bounds.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb bounds.lc) (Nat.zero_le k)
  have hc (k : ℕ) : Exp.lcb k (Occil.General.refinedCDFComparison : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb comparison_lc) (Nat.zero_le k)
  simp [search, searchCode, Exp.lcb, hb, hc]

theorem open_bag {rT : Type} [ProbLangℝ rT] (size : ℤ) (bounds : Val rT) (l : Loc) :
    Exp.open' (bagBody size bounds) (Val.loc l).fst =
      pl(let decide := &(search bounds l); decide #0 (#int size - #1)) := by
  simp [bagBody, startCode, search, searchCode, Exp.open', Exp.openRec,
    comparison_openRec, (Exp.open_lc 4 (Val.loc l).fst bounds.fst bounds.lc).symm]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

/-- Open all source parameters and the positive-size guard before allocating the shared bag. -/
theorem twp_open (E : CoPset) (size : ℕ) (hsize : 0 < size) (bounds : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E (.app (.lam (bagBody size bounds)) pl(&Occil.newUniformBag #())) Φ ⊢
      tglWp E pl(&Occil.General.incompleteInformation #int (size : ℤ) &bounds.fst #()) Φ := by
  iintro H
  rw [source_eq]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL bounds, .appL Val.unit]
      (.app (.lam sourceBody) (Val.int (size : ℤ)).fst)) Φ)
  iapply (twp_beta E [.appL bounds, .appL Val.unit] sourceBody (Val.int (size : ℤ))
    source_lc Φ)
  rw [open_size]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL Val.unit]
      (.app (.lam (boundsBody size)) bounds.fst)) Φ)
  iapply (twp_beta E [.appL Val.unit] (boundsBody size) bounds (bounds_lc size) Φ)
  rw [open_bounds]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [] (.app (.lam (unitBody size bounds)) Val.unit.fst)) Φ)
  iapply (twp_beta E [] (unitBody size bounds) Val.unit (unit_lc size bounds) Φ)
  rw [open_unit]
  ieval (change _ ⊢ tglWp E (unitBody size bounds) Φ)
  twp_pure
  have hguard : decide ((size : ℤ) ≤ 0) = false := by
    exact decide_eq_false (show ¬(size : ℤ) ≤ 0 from by omega)
  rw [hguard]
  twp_pure
  iexact H

/-- The allocated root is substituted without unfolding the recursive search closure. -/
theorem twp_open_bag (E : CoPset) (size : ℤ) (bounds : Val rT) (l : Loc)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(search bounds l) #0 #int (size - 1)) Φ ⊢
      tglWp E (.app (.lam (bagBody size bounds)) (Exp.ofVal (Val.loc l))) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill []
      (.app (.lam (bagBody size bounds)) (Val.loc l).fst)) Φ)
  iapply (twp_beta E [] (bagBody size bounds) (Val.loc l) (bag_lc size bounds) Φ)
  ieval (change _ ⊢ tglWp E ((bagBody size bounds).open' (Val.loc l).fst) Φ)
  rw [open_bag]
  let code : Val rT := ⟨search bounds l, .fix (search_lc bounds l), search_lc bounds l⟩
  ieval (
    change _ ⊢ tglWp E (Ectx.fill []
      (.app (.lam pl(⟪bvar 0⟫ #0 (#int size - #1))) code.fst)) Φ)
  iapply (twp_beta E [] pl(⟪bvar 0⟫ #0 (#int size - #1)) code (by is_lc) Φ)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec, code, ↓reduceIte]
  twp_pure
  iexact H

end specification

end SampLib.IncompleteInformation.Program
