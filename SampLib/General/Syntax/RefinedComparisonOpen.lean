import SampLib.General.Syntax.RefinedComparison

/-! # Opening the dyadic refinement sources

These steps reduce each source to its recursive comparison loop. They keep the loop body
opaque, so later proofs see only the next action.
-/

open ProbLang

namespace SampLib.RefinedComparison.Program

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
