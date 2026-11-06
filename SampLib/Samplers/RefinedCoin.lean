import SampLib.RefinedComparison

/-! # Exact coins from converging dyadic bounds

The bounds need not be nested or have a known convergence rate. Each bound must
contain the same target probability, including either endpoint of the unit interval.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RefinedCoin

open RefinedComparison.Program

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- One fresh latent uniform is retained throughout all refinements. -/
theorem twp_refinedCoin (E : CoPset) (p : unitInterval)
    (a : ℕ → FromBounds.Interval p) (ha : FromBounds.Tight a)
    (hlo : ∀ n, 0 ≤ (a n).lower) (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (bounds : Val rT)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a n)⌝))) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit p F) -∗
      tglWp E pl(&Occil.General.refinedCoin &bounds.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  isimp only [← RefinedComparison.constant_expectation p F] at Hcredit
  iapply twp_open_coin E bounds _
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  iapply twp_open_coin_bag E bounds l _
  have hloop := RefinedComparison.twp_loop E p a ha hlo hhi hden bounds.fst bounds.lc
    hbounds l [] (fun b _ => F b) (fun _ => measurable_const)
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply hloop
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [RefinedComparison.post] at Hpost
  ihave ⟨%b, %q, %hq, Hbag, Hcredit⟩ := Hpost
  rcases hq with ⟨rfl, _, _⟩
  isimp only [DyadicPosterior.credit, MeasureTheory.lintegral_const,
    MeasureTheory.measure_univ, mul_one] at Hcredit
  iexists b
  iframe Hcredit
  itrivial

/-- Exact Bernoulli sampling from arbitrarily tight, valid dyadic enclosures. -/
theorem refinedCoin_distSpec (E : CoPset) (p : unitInterval)
    (a : ℕ → FromBounds.Interval p) (ha : FromBounds.Tight a)
    (hlo : ∀ n, 0 ≤ (a n).lower) (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (bounds : Val rT)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a n)⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.General.refinedCoin &bounds.fst #())
      (RealCoin.law p) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_refinedCoin E p a ha hlo hhi hden bounds hbounds F)

end

end SampLib.RefinedCoin
