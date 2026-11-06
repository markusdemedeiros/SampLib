import SampLib.Bernoulli.PolynomialFactory
import SampLib.Bernoulli.Syntax.PolynomialRational
import Metrology.Iris.LocalBI

/-! # Rational factories from two power-basis polynomials

Each polynomial search has an admissible degree. A Bernoulli race then samples
`A(p)/(A(p)+B(p))`, requiring positivity only at the supplied input bias.
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

private theorem polynomial_callback (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs : List Fraction) (hxs : xs ≠ []) (H : ∃ n, Admissible xs n) :
    IsDistSpec (GF := GF) E pl(&(RationalProgram.polynomialValue coin xs).fst #())
      (RealCoin.law (bias xs hxs H p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    ieval (
      change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
        (.app (.lam (RationalProgram.polynomialCall coin xs)) (Val.unit : Val rT).fst)) _)
    iapply (twp_beta E [] (RationalProgram.polynomialCall coin xs) Val.unit
      (RationalProgram.polynomialValue coin xs).lc _)
    ieval (
      change _ ⊢ tglWp E
        (Exp.open' (RationalProgram.polynomialCall coin xs) (Val.unit : Val rT).fst) _)
    isimp only [Exp.open']
    rw [← Exp.open_lc 0 Val.unit.fst _ (RationalProgram.call_lc coin xs)]
    isimp only [RationalProgram.polynomialCall]
    iapply (polynomial_distSpec E p coin hcoin xs hxs H).spec F hF $$ Hcredit

/-- The unchanged source race, on the full admissible-polynomial domain. -/
theorem twp_rationalFunction (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs ys : List Fraction) (hxs : xs ≠ []) (hys : ys ≠ [])
    (Hx : ∃ n, Admissible xs n) (Hy : ∃ n, Admissible ys n)
    (hpos : 0 < value xs p + value ys p) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (BernoulliRace.credit (bias xs hxs Hx p) (bias ys hys Hy p) F) -∗
      tglWp E pl(&Occil.FactoryExtra.rationalFunction &coin.fst
        &(listVal Fraction.encode xs).fst &(listVal Fraction.encode ys).fst #())
        (post F) := by
  iintro Hcredit
  iapply (RationalProgram.twp_open E coin xs ys (post F))
  isimp only [BernoulliRace.credit, ← RealCoin.lintegral_law] at Hcredit
  iapply ((BernoulliRace.bernoulliRace_distSpec E (bias xs hxs Hx p) (bias ys hys Hy p) hpos
    (RationalProgram.polynomialValue coin xs) (RationalProgram.polynomialValue coin ys)
    (polynomial_callback E p coin hcoin xs hxs Hx)
    (polynomial_callback E p coin hcoin ys hys Hy)).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  isimp only [post]
  iexists b
  iframe Hcredit
  itrivial

/-- `A(p)/(A(p)+B(p))`, with any admissible inputs and positive combined value. -/
theorem rationalFunction_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (xs ys : List Fraction) (hxs : xs ≠ []) (hys : ys ≠ [])
    (Hx : ∃ n, Admissible xs n) (Hy : ∃ n, Admissible ys n)
    (hpos : 0 < value xs p + value ys p) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.rationalFunction &coin.fst
      &(listVal Fraction.encode xs).fst &(listVal Fraction.encode ys).fst #())
      (BernoulliRace.law (bias xs hxs Hx p) (bias ys hys Hy p)) Val.bool where
  spec F _ := by
    rw [RealCoin.lintegral_law]
    exact wand_entails (twp_rationalFunction E p coin hcoin xs ys hxs hys Hx Hy hpos F)

end specification

end SampLib.PolynomialFactory
