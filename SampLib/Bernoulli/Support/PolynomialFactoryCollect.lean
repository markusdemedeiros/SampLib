import SampLib.Bernoulli.Support.PolynomialFactoryTerms
import SampLib.Bernoulli.Support.PolynomialFactoryTable

/-! Constructing the complete coefficient table, in the source's evaluation order. -/

open ProbLang

namespace SampLib.PolynomialFactory

open FactoryFractions

def tableFrom (xs : List Fraction) (n k steps : ℕ) : List Fraction :=
  (List.range' k steps).map (fun j => Fraction.ofRat (coefficient xs n j))

theorem tableFrom_zero (xs : List Fraction) (n : ℕ) :
    tableFrom xs n 0 (n + 1) = table xs n := by
  unfold tableFrom table
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul,
      List.getElem_ofFn]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_collect (E : CoPset) (xs : List Fraction) (hxs : xs ≠ [])
    (n : ℕ) (hn : degree xs ≤ n) (k steps : ℕ) (hsteps : k + steps = n + 1) :
    ⊢ tglWp E pl(&(Syntax.collect xs n) #int (k : ℤ))
      (fun v : Val rT => iprop(⌜v = listVal Fraction.encode (tableFrom xs n k steps)⌝)) := by
  rw [Syntax.collect_eq]
  induction steps generalizing k with
  | zero =>
    have htest : decide ((n : ℤ) < k) = true := decide_eq_true (by omega)
    isimp only [Syntax.collectCode, Syntax.collectBody]
    twp_pures
    rw [htest]
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp [tableFrom, listVal]
  | succ steps IH =>
    have htest : decide ((n : ℤ) < k) = false := decide_eq_false (by omega)
    isimp only [Syntax.collectCode, Syntax.collectBody]
    twp_pures
    rw [htest]
    iterate 2 twp_pure
    isimp only [ClosedExp.openRec, Nat.cast_add_one]
    twp_bind pl(&(Syntax.collectCode xs n) #int ((k + 1 : ℕ) : ℤ))
    isimp only [Nat.cast_add_one]
    iapply tglWp_wand
    isplitl []
    · have h := IH (k + 1) (by omega)
      simp only [Nat.cast_add_one] at h
      iapply h
    iintro %v %hv
    subst v
    twp_bind pl(&(Syntax.coefficient xs n) #int (k : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply twp_coefficient E xs hxs n k hn
    iintro %v %hv
    subst v
    change ⊢ tglWp E (Exp.ofVal (listVal Fraction.encode
      (Fraction.ofRat (coefficient xs n k) :: tableFrom xs n (k + 1) steps)))
      (fun v : Val rT => iprop(⌜v = listVal Fraction.encode (tableFrom xs n k (steps + 1))⌝))
    iapply tglWp_value
    ipureintro
    simp [tableFrom, List.range'_succ]

end specification

end SampLib.PolynomialFactory
