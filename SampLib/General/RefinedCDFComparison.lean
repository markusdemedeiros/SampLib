import SampLib.General.Support.RefinedComparison

/-! # Exact comparison with an incompletely known CDF value

The original cache is retained. Both continuation credit and the learned
comparison fact refer to its same latent uniform, not to a fresh independent draw.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RefinedCDFComparison

open RefinedComparison.Program

noncomputable section

/-- A threshold is a deterministic Bernoulli kernel conditional on the latent uniform. -/
theorem threshold_kernel (p : unitInterval) (G : Bool → ℝ → ℝ≥0∞) :
    LatentBernoulli.kernel (RefinedComparison.threshold p) G =
      RefinedComparison.outputCredit p G := by
  funext u
  by_cases h : u < (p : ℝ) <;>
    simp [LatentBernoulli.kernel, RefinedComparison.threshold,
      RefinedComparison.outputCredit, RealCoin.credit, RealCoin.pmf, h]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The actual indexed comparison returns its refined cache and exact threshold relation. -/
theorem twp_refinedCDFComparison (E : CoPset) (p : unitInterval)
    (a : ℕ → FromBounds.Interval p) (ha : FromBounds.Tight a)
    (hlo : ∀ n, 0 ≤ (a n).lower) (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (bounds : Val rT) (index : ℤ)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int index #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a n)⌝)))
    (l : Loc) (q : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l q ∗
      ↯ (DyadicPosterior.credit q (RefinedComparison.outputCredit p G))) ⊢
      tglWp E pl(&Occil.General.refinedCDFComparison #loc l &bounds.fst #int index)
        (RefinedComparison.post l q p G) := by
  iintro Hcredit
  iapply twp_open_comparison E bounds l index _
  have hlookup : pl(&bounds.fst #int index).IsLocallyClosed := by is_lc
  iapply RefinedComparison.twp_loop E p a ha hlo hhi hden
    pl(&bounds.fst #int index) hlookup hbounds l q G hG
  iframe Hcredit

/-- A reusable joint specification, preserving correlations through subsequent comparisons. -/
theorem refinedCDFComparison_coinSpec (E : CoPset) (p : unitInterval)
    (a : ℕ → FromBounds.Interval p) (ha : FromBounds.Tight a)
    (hlo : ∀ n, 0 ≤ (a n).lower) (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (bounds : Val rT) (index : ℤ)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int index #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a n)⌝))) (l : Loc) :
    UniformBag.IsCoinSpec (GF := GF) E l
      pl(&Occil.General.refinedCDFComparison #loc l &bounds.fst #int index)
      (RefinedComparison.threshold p) where
  measurable_bias := RefinedComparison.measurable_threshold p
  spec q G hG := by
    iintro Hcredit
    isimp only [LatentBernoulli.credit, threshold_kernel] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply twp_refinedCDFComparison E p a ha hlo hhi hden bounds index hbounds l q G hG
      iframe Hcredit
    iintro %v Hpost
    isimp only [RefinedComparison.post] at Hpost
    ihave ⟨%b, %r, %hr, Hbag, Hcredit⟩ := Hpost
    isimp only [UniformBag.coinPost]
    iexists b, r
    iframe Hbag Hcredit
    ipureintro
    exact ⟨hr.1, hr.2.1⟩

end specification

end

end SampLib.RefinedCDFComparison
