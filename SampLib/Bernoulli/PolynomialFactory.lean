import SampLib.Bernoulli.Support.PolynomialFactoryCollect
import SampLib.Bernoulli.Syntax.PolynomialFactoryOpen
import Metrology.Iris.LocalBI

/-! # Power-basis polynomial factories

The deterministic source search terminates at any supplied admissible degree.
Every successful conversion represents the same polynomial, so the Bernstein
sampler at the first accepted degree has the desired law.
-/

open ProbLang
open scoped unitInterval ENNReal

namespace SampLib.PolynomialFactory

open FactoryFractions

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private noncomputable def post (F : Bool → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))

private theorem twp_search (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Fraction) (hxs : xs ≠ []) (H : ∃ n, Admissible xs n)
    (N : ℕ) (hN : Admissible xs N) (steps n : ℕ)
    (hn : degree xs ≤ n) (hsteps : n + steps = N) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias xs hxs H p) F) -∗
      tglWp E pl(&(Source.convert coin xs) #int (n : ℤ))
        (post F) := by
  induction steps using Nat.strong_induction_on generalizing n with
  | h steps IH =>
    iintro Hcredit
    iapply (Source.twp_round E coin xs n (post F))
    twp_bind pl(&(Syntax.collectCode xs n) #0)
    iapply tglWp_wand
    isplitl []
    · have h := twp_collect (rT := rT) (GF := GF) E xs hxs n hn 0 (n + 1) (by simp)
      rw [Syntax.collect_eq] at h
      simp only [tableFrom_zero] at h
      iapply h
    iintro %v %hv
    subst v
    isimp only [Exp.ofVal]
    iapply (Source.twp_table E coin xs n (listVal Fraction.encode (table xs n)) (post F))
    unfold Source.branchCode
    twp_bind pl(&Syntax.check &(listVal Fraction.encode (table xs n)).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_check
    iintro %v %hv
    subst v
    by_cases hv : valid (table xs n) = true
    · rw [hv]
      twp_pure
      have ha : Admissible xs n := ⟨hn, (valid_table xs n).mp hv⟩
      rw [encoding_table xs n ha]
      let : NeZero (probabilityTable xs n ha).length := ⟨by simp⟩
      isimp only [← RealCoin.lintegral_law,
        ← probabilityTable_law xs hxs H n ha p] at Hcredit
      iapply ((BernsteinFactory.bernsteinFactory_distSpec E p coin hcoin
        (probabilityTable xs n ha)).wp F (measurable_of_countable _) _) $$ Hcredit
      iintro %b Hcredit
      isimp only [post]
      iexists b
      isplitr [Hcredit]
      · ipureintro
        rfl
      · iexact Hcredit
    · have hv' : valid (table xs n) = false := Bool.eq_false_iff.mpr hv
      rw [hv']
      iterate 2 twp_pure
      have hnN := search_progress xs n N (by omega) hN hv
      have hrec := IH (steps - 1) (by omega) (n + 1) (by omega) (by omega)
      simp only [Nat.cast_add_one] at hrec
      iapply hrec $$ Hcredit

/-- The actual automatic-elevation algorithm on its algebraic termination domain. -/
theorem twp_polynomial (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Fraction) (hxs : xs ≠ []) (H : ∃ n, Admissible xs n)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias xs hxs H p) F) -∗
      tglWp E pl(&Occil.FactoryExtra.polynomial &coin.fst
        &(listVal Fraction.encode xs).fst #())
        (post F) := by
  iintro Hcredit
  iapply Source.twp_open E coin xs hxs
  iapply (twp_search E p coin hcoin xs hxs H H.choose H.choose_spec
    (H.choose - degree xs) (degree xs) le_rfl (by have := H.choose_spec.1; omega) F) $$ Hcredit

/-- Power-basis polynomial sampling, including exact endpoint-valued polynomials. -/
theorem polynomial_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Fraction) (hxs : xs ≠ []) (H : ∃ n, Admissible xs n) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.polynomial &coin.fst
      &(listVal Fraction.encode xs).fst #()) (RealCoin.law (bias xs hxs H p)) Val.bool where
  spec F _ := by
    rw [RealCoin.lintegral_law]
    exact wand_entails (twp_polynomial E p coin hcoin xs hxs H F)

/-- Strict range on the closed unit interval supplies the search's termination witness. -/
theorem polynomial_strict_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Fraction) (hxs : xs ≠ [])
    (h : ∀ x : unitInterval, value xs x ∈ Set.Ioo 0 1) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.polynomial &coin.fst
      &(listVal Fraction.encode xs).fst #())
      (RealCoin.law (bias xs hxs (exists_admissible xs hxs h) p)) Val.bool :=
  polynomial_distSpec E p coin hcoin xs hxs (exists_admissible xs hxs h)

end specification

end SampLib.PolynomialFactory
