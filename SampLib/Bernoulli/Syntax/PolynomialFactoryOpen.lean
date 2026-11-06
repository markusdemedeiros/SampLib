import SampLib.Bernoulli.Syntax.PolynomialFactoryRound

/-! # Opening the polynomial factory

Initializing the actual polynomial factory, without inspecting its coin callback.
-/

open ProbLang

namespace SampLib.PolynomialFactory.Source

open FactoryFractions

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Bind the supplied data, compute its degree, and start the unchanged source search. -/
theorem twp_open (E : CoPset) (coin : Val rT) (xs : List Fraction) (hxs : xs ≠ [])
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&(convert coin xs) #int (degree xs : ℤ)) Φ ⊢
      tglWp E pl(&Occil.FactoryExtra.polynomial &coin.fst
        &(listVal Fraction.encode xs).fst #()) Φ := by
  rw [source_eq]
  iintro H
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill [.appL (listVal Fraction.encode xs), .appL Val.unit]
        (.app (.lam sourceBody) coin.fst)) Φ)
  iapply (twp_beta E [.appL (listVal Fraction.encode xs), .appL Val.unit]
    sourceBody coin source_lc Φ)
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill [.appL Val.unit]
        (.app (.lam (coefficientsBody coin)) (listVal Fraction.encode xs).fst)) Φ)
  iapply (twp_beta E [.appL Val.unit] (coefficientsBody coin)
    (listVal Fraction.encode xs) (coefficients_lc coin) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (unitBody coin xs)) (Val.unit : Val rT).fst)) Φ)
  iapply (twp_beta E [] (unitBody coin xs) Val.unit (unit_lc coin xs) Φ)
  ieval (change _ ⊢ tglWp E (initialBody coin xs) Φ)
  rw [initial_eq]
  twp_bind pl(&Occil.length &(listVal Fraction.encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length
  iintro %v %hv
  subst v
  twp_pure
  have hd : (xs.length : ℤ) - 1 = (degree xs : ℤ) := by
    have := List.length_pos_iff.mpr hxs
    simp only [degree]
    omega
  rw [hd]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (degreeBody coin xs)) (Val.int (degree xs : ℤ)).fst)) Φ)
  iapply (twp_beta E [] (degreeBody coin xs) (Val.int (degree xs : ℤ))
    (degree_lc coin xs) Φ)
  ieval (
    change _ ⊢ tglWp E (Exp.open' (degreeBody coin xs) (Val.int (degree xs : ℤ)).fst) Φ)
  rw [opened_degree]
  twp_pure
  twp_pure
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (.app (.bvar 0) (Val.int (degree xs : ℤ)).fst)) (convertValue coin xs).fst)) Φ)
  iapply (twp_beta E [] (.app (.bvar 0) (Val.int (degree xs : ℤ)).fst)
    (convertValue coin xs) (by is_lc) Φ)
  ieval (change _ ⊢ tglWp E pl(&(convert coin xs) #int (degree xs : ℤ)) Φ)
  iexact H

end specification

end SampLib.PolynomialFactory.Source
