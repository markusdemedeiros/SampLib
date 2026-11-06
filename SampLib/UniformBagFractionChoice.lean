import SampLib.UniformBagChoice
import SampLib.FactoryFractions

/-! # Choosing with a raw rational threshold on one cached uniform -/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

open FactoryFractions

noncomputable section

def fractionChoice {rT : Type} (l : Loc) (a : Fraction) (yes no : Exp rT) : Exp rT :=
  .cond pl(&Occil.uniformBagLess #loc l (fst(&a.encode.fst)) (snd(&a.encode.fst))) yes no

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Both branches retain the refined bag, its original latent credit, and the comparison fact. -/
theorem twp_fractionChoice (E : CoPset) (l : Loc) (a : Fraction) (q : List Bool)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (yes no : Exp rT) (Φ : Val rT → IProp GF)
    (hyes : ∀ s : List Bool, q <+: s → DyadicPosterior.resolves s (a.value : ℝ) true →
      iprop(owns l s ∗ ↯ (DyadicPosterior.credit s G)) ⊢ tglWp E yes Φ)
    (hno : ∀ s : List Bool, q <+: s → DyadicPosterior.resolves s (a.value : ℝ) false →
      iprop(owns l s ∗ ↯ (DyadicPosterior.credit s G)) ⊢ tglWp E no Φ) :
    iprop(owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢
      tglWp E (fractionChoice l a yes no) Φ := by
  iintro H
  iterate 2 twp_pure
  simp only [Exp.ofVal]
  ieval (
    change _ ⊢ tglWp E (choice l a.numerator a.denominator yes no) Φ)
  iapply twp_choice E l q a.numerator a.denominator
    (by exact_mod_cast a.positive) G hG yes no Φ ?_ ?_
  · intro s hs ht
    iapply hyes s hs (by simpa only [Fraction.cast_value, Int.cast_natCast] using ht)
  · intro s hs ht
    iapply hno s hs (by simpa only [Fraction.cast_value, Int.cast_natCast] using ht)
  · iexact H

end specification

end

end SampLib.UniformBag
