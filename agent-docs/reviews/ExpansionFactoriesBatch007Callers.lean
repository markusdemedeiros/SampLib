import SampLib.Samplers.ExpMinusPolynomial
import SampLib.UniformBagLess
import SampLib.UniformBagPrefix
import SampLib.UniformBagComparison
import SampLib.Distributions.DyadicRefinement
import SampLib.UniformBag
import SampLib.Templates
import Metrology.Iris.LocalBI

open ProbLang
open scoped ENNReal

namespace ExpansionFactoriesReview

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem frame {E : CoPset} {e : Exp rT} {μ : MeasureTheory.Measure Bool}
    [MeasureTheory.IsProbabilityMeasure μ]
    (h : IsDistSpec (GF := GF) E e μ Val.bool) (F : Bool → ℝ≥0∞) (I : IProp GF) :
    ⊢ ↯ (∫⁻ b, F b ∂μ) ∗ I -∗ tglWp E e
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply (h.wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  iexists b
  iframe Hcredit HI
  itrivial


variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (I : IProp GF) :
    I ⊢ tglWp E pl(&Occil.newUniformBag #())
      (fun v : Val rT => iprop(∃ l : Loc,
        ⌜v = Val.loc l⌝ ∗ UniformBag.owns l [] ∗ I)) := by
  iintro HI
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag
  iintro %v ⟨%l, %hv, Hl⟩
  iexists l
  iframe Hl HI
  itrivial

example (E : CoPset) (l : Loc) (K : Bool → ℝ≥0∞) (I : IProp GF) :
    iprop((UniformBag.owns l [] ∗ ↯ (∫⁻ b, K b ∂RealCoin.law VonNeumann.fairBias)) ∗ I) ⊢
      tglWp E pl(&Occil.uniformBagStep #loc l)
        (fun v : Val rT => iprop(∃ (b : Bool) (tail : Loc),
          ⌜v = Val.pair (Val.bool b) (Val.loc tail)⌝ ∗
          appHeapFrag l (UniformBag.nodeVal b tail) ∗ UniformBag.owns tail [] ∗ ↯ (K b) ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply UniformBag.twp_freshStep E l K $$ Hbag
  iintro %v ⟨%b, %tail, %hv, Hl, Htail, Hcredit⟩
  iexists b, tail
  iframe Hl Htail Hcredit HI
  itrivial

example (E : CoPset) (l : Loc) (p : List Bool) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (DyadicPosterior.credit p F)) ∗ I) ⊢
      tglWp E pl(&Occil.uniformBagStep #loc l)
        (fun v : Val rT => iprop(∃ (b : Bool) (tail : Loc) (q : List Bool),
          ⌜v = Val.pair (Val.bool b) (Val.loc tail) ∧ UniformBag.stepRefines p b q⌝ ∗
          appHeapFrag l (UniformBag.nodeVal b tail) ∗ UniformBag.owns tail q ∗
          ↯ (DyadicPosterior.credit (b :: q) F) ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply UniformBag.twp_uniformBagStep E l p F hF $$ Hbag
  iintro %v ⟨%b, %tail, %q, %hv, Hl, Htail, Hcredit⟩
  iexists b, tail, q
  iframe Hl Htail Hcredit HI
  itrivial

example (head b : Bool) (p q : List Bool)
    (h : UniformBag.stepRefines (head :: p) b q) : head = b ∧ p = q := by
  rcases h with h | h
  · cases h.1
  · exact List.cons.inj h

example (p : List Bool) : DyadicPosterior.credit p (fun _ => ∞) = ∞ := by
  rw [DyadicPosterior.credit, MeasureTheory.lintegral_const, MeasureTheory.measure_univ,
    mul_one]
example (p : List Bool) : DyadicPosterior.credit p (fun _ => 0) = 0 := by
  simp [DyadicPosterior.credit]
example (p : List Bool) (x : ℝ) : DyadicPosterior.law p {x} = 0 := by simp
example (p : List Bool) :
    (DyadicPosterior.law p).map (fun _ => ()) = MeasureTheory.Measure.dirac () := by
  simp
example (p : List Bool) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    DyadicPosterior.credit p F =
      (DyadicPosterior.credit (p ++ [false]) F +
        DyadicPosterior.credit (p ++ [true]) F) / 2 :=
  DyadicPosterior.credit_split p F hF
example (p : List Bool) : DyadicPosterior.resolves p 0 false :=
  DyadicPosterior.resolves_false p le_rfl
example (p : List Bool) : DyadicPosterior.resolves p 1 true :=
  DyadicPosterior.resolves_true p le_rfl
example (p : List Bool) :
    DyadicPosterior.resolves (false :: p) (1/2) true := by
  rw [DyadicPosterior.resolves_cons]
  norm_num
  exact DyadicPosterior.resolves_true p le_rfl
example (p : List Bool) :
    DyadicPosterior.resolves (true :: p) (1/2) false := by
  rw [DyadicPosterior.resolves_cons]
  norm_num
  exact DyadicPosterior.resolves_false p le_rfl

example (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hc : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (cs : List ExpMinusPolynomial.Coefficient) (F : Bool → ℝ≥0∞) (I : IProp GF) :=
  frame (ExpMinusPolynomial.expMinusPolynomial_distSpec E p coin hc cs) F I

private def halfCoefficient : ExpMinusPolynomial.Coefficient := ⟨(1,2), by decide⟩
private def zeroCoefficient : ExpMinusPolynomial.Coefficient := ⟨(0,1), by decide⟩

example (p : unitInterval) :
    ExpMinusPolynomial.value p [halfCoefficient, zeroCoefficient, halfCoefficient] 0 =
      (1:ℝ)/2 + (1:ℝ)/2*(p:ℝ)^2 := by
  norm_num [ExpMinusPolynomial.value, halfCoefficient, zeroCoefficient]
example : ExpMinusPolynomial.value 0 [halfCoefficient, halfCoefficient] 0 = (1:ℝ)/2 := by
  norm_num [ExpMinusPolynomial.value, halfCoefficient]
example : ExpMinusPolynomial.value 1 [halfCoefficient, halfCoefficient] 0 = 1 := by
  norm_num [ExpMinusPolynomial.value, halfCoefficient]
example (p : unitInterval) :
    (ExpMinusPolynomial.bias p [halfCoefficient] 0 : ℝ) = Real.exp (-(1:ℝ)/2) := by
  norm_num [ExpMinusPolynomial.bias, ExpMinusPolynomial.value, halfCoefficient]
example (p : unitInterval) : ExpMinusPolynomial.bias p [] 0 = 1 := by
  apply Subtype.ext
  simp [ExpMinusPolynomial.bias, ExpMinusPolynomial.value]
example (p : unitInterval) :
    RealCoin.credit (ExpMinusPolynomial.bias p [] 0) (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ExpMinusPolynomial.bias, ExpMinusPolynomial.value]
example (p : unitInterval) :
    RealCoin.credit (ExpMinusPolynomial.bias p [zeroCoefficient, zeroCoefficient] 0)
      (fun b => if b then 0 else ∞) = 0 := by
  simp [RealCoin.credit, RealCoin.pmf, ExpMinusPolynomial.bias,
    ExpMinusPolynomial.value, zeroCoefficient]

example (E : CoPset) (l : Loc) (p : List Bool) (n : ℕ) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (DyadicPosterior.credit p F)) ∗ I) ⊢
      tglWp E pl(&Occil.uniformBagPrefix #loc l #int (n : ℤ))
        (fun v : Val rT => iprop(∃ q : List Bool,
          ⌜UniformBag.readRefines p n q ∧ v = Val.int (UniformBag.rank (q.take n))⌝ ∗
          UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q F) ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply UniformBag.twp_uniformBagPrefix E l p n F hF $$ Hbag
  iintro %v ⟨%q, %hq, Hbag, Hcredit⟩
  iexists q
  iframe Hbag Hcredit HI
  itrivial

example : UniformBag.rank [true, false, true] = 5 := by decide
example : UniformBag.rank [false, true] = 1 := by decide
example : UniformBag.readRefines [true, false] 1 [true, false] := by
  simp [UniformBag.readRefines]
example (p q : List Bool) (hp : p <+: q) :
    MeasureTheory.Measure.AbsolutelyContinuous (DyadicPosterior.law q) (DyadicPosterior.law p) :=
  DyadicPosterior.law_refines hp
example (p q : List Bool) (hp : p <+: q) (t : ℝ) (b : Bool)
    (h : DyadicPosterior.resolves p t b) : DyadicPosterior.resolves q t b :=
  DyadicPosterior.resolves_refines hp h
example (retry : Bool) (ε : ℝ≥0∞) :
    (∫⁻ b, UniformBag.comparisonCredit (fun _ => 0) retry ε b
      ∂RealCoin.law VonNeumann.fairBias) = ε := by
  rw [UniformBag.comparison_expectation _ measurable_const]
  simp [DyadicPosterior.credit]
example (p : List Bool) :
    DyadicPosterior.resolves (false :: p) (1/2) true := by
  simpa using UniformBag.exit_resolves p 1 2 (by decide) false (by decide)

example (E : CoPset) (l : Loc) (p : List Bool) (x y : ℤ) (hy : 0 < y)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (DyadicPosterior.credit p F)) ∗ I) ⊢
      tglWp E pl(&Occil.uniformBagLess #loc l #int x #int y)
        (fun v : Val rT => iprop(UniformBag.lessPost l p x y F v ∗ I)) := by
  iintro ⟨Hbag, HI⟩
  iapply tglWp_wand
  isplitl [Hbag]
  · iapply UniformBag.twp_uniformBagLess E l p x y hy F hF $$ Hbag
  iintro %v Hpost
  iframe Hpost HI

private theorem resolves_unique (p : List Bool) (t : ℝ) (b c : Bool)
    (hb : DyadicPosterior.resolves p t b) (hc : DyadicPosterior.resolves p t c) : b = c := by
  obtain ⟨u, hu, hv⟩ := (hb.and hc).exists
  exact hu.symm.trans hv

-- Reusing the same bag gives consistent results and keeps the entire refined cache.
example (E : CoPset) (l : Loc) (p : List Bool) (x y : ℤ) (hy : 0 < y)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    iprop((UniformBag.owns l p ∗ ↯ (DyadicPosterior.credit p F)) ∗ I) ⊢
      tglWp E pl(let first := &Occil.uniformBagLess #loc l #int x #int y;
        let second := &Occil.uniformBagLess #loc l #int x #int y;
        (first, second))
        (fun v : Val rT => iprop(∃ (b : Bool) (q : List Bool),
          ⌜v = Val.pair (Val.bool b) (Val.bool b) ∧ p <+: q ∧
            DyadicPosterior.resolves q ((x : ℝ)/y) b⌝ ∗
          UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q F) ∗ I)) := by
  iintro ⟨⟨Hbag, Hcredit⟩, HI⟩
  twp_bind pl(&Occil.uniformBagLess #loc l #int x #int y)
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply UniformBag.twp_uniformBagLess E l p x y hy F hF
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [UniformBag.lessPost] at Hpost
  ihave ⟨%b, %q, %hb, Hbag, Hcredit⟩ := Hpost
  rcases hb with ⟨rfl, hpq, hb⟩
  twp_pure
  twp_bind pl(&Occil.uniformBagLess #loc l #int x #int y)
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply UniformBag.twp_uniformBagLess E l q x y hy F hF
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [UniformBag.lessPost] at Hpost
  ihave ⟨%c, %r, %hc, Hbag, Hcredit⟩ := Hpost
  rcases hc with ⟨rfl, hqr, hc⟩
  have hb' := DyadicPosterior.resolves_refines hqr hb
  have hbc := resolves_unique r ((x : ℝ)/y) b c hb' hc
  subst c
  twp_pures
  twp_value
  imodintro
  iexists b, r
  iframe Hbag Hcredit HI
  ipureintro
  exact ⟨rfl, hpq.trans hqr, hb'⟩

#print axioms SampLib.UniformBag.twp_uniformBagLess


#print axioms SampLib.UniformBag.twp_uniformBagPrefix
#print axioms SampLib.DyadicPosterior.law_refines
#print axioms SampLib.UniformBag.comparison_expectation
#print axioms SampLib.UniformBag.exit_resolves

#print axioms SampLib.ExpMinusPolynomial.expMinusPolynomial_distSpec
#print axioms SampLib.ExpMinusPolynomial.expectation

#print axioms SampLib.UniformBag.twp_newUniformBag
#print axioms SampLib.UniformBag.twp_freshStep
#print axioms SampLib.UniformBag.twp_uniformBagStep
#print axioms SampLib.DyadicPosterior.law_eq_uniform
#print axioms SampLib.DyadicPosterior.credit_split
#print axioms SampLib.DyadicPosterior.resolves_cons

end
end ExpansionFactoriesReview
