import SampLib.Samplers.RefinedCoin
import SampLib.Samplers.RefinedCDFComparison
import SampLib.Samplers.IncompleteInformation
import SampLib.PSRNIntegerPower

open ProbLang
open scoped ENNReal

namespace ReviewExactStructured004

noncomputable section

open SampLib

private def endpoint (b : Bool) : unitInterval := if b then 1 else 0

private def enclosure (b : Bool) (n : ℕ) : FromBounds.Interval (endpoint b) where
  lower := if b then (2 : ℤ) ^ (n + 1) else 0
  upper := if b then (2 : ℤ) ^ (n + 1) else 0
  denominator := 2 ^ (n + 1)
  positive := by positivity
  below := by cases b <;> simp [endpoint]
  above := by cases b <;> simp [endpoint]

private theorem tight (b : Bool) : FromBounds.Tight (enclosure b) := by
  intro ε hε
  exact ⟨0, by simpa [FromBounds.Interval.width, FromBounds.Interval.left,
    FromBounds.Interval.right, enclosure] using hε.le⟩

private theorem lower_nonneg (b : Bool) (n : ℕ) : 0 ≤ (enclosure b n).lower := by
  cases b <;> simp [enclosure]

private theorem upper_le (b : Bool) (n : ℕ) :
    (enclosure b n).upper ≤ (enclosure b n).denominator := by
  cases b <;> simp [enclosure]

/-- A plateau CDF with three zero-mass positions and one certain outcome. -/
private def cdfModel : IncompleteInformation.Model where
  size := 4
  positive := by decide
  cdf x := endpoint (decide (3 ≤ x))
  monotone := by
    intro x hx y hy hxy
    by_cases h : 3 ≤ x
    · have hy' : 3 ≤ y := h.trans hxy
      simp [endpoint, h, hy']
    · simp only [endpoint, decide_eq_false h, Bool.false_eq_true, ite_false]
      exact (endpoint _).property.1
  upper_mass := by norm_num [endpoint]

example : IncompleteInformation.law cdfModel (Set.Iic 2) = 0 := by
  rw [IncompleteInformation.cdf cdfModel 2 (by norm_num [cdfModel,
    IncompleteInformation.Model.upper])]
  norm_num [cdfModel, endpoint]

example : IncompleteInformation.law cdfModel (Set.Iic 3) = 1 := by
  rw [IncompleteInformation.cdf cdfModel 3 (by norm_num [cdfModel,
    IncompleteInformation.Model.upper])]
  norm_num [cdfModel, endpoint]

section callers

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
theorem frame {α : Type _} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ] {E : CoPset} {e : Exp rT}
    {encode : α → Val rT} (h : IsDistSpec (GF := GF) E e μ encode)
    (F : α → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂μ) ∗ R -∗ tglWp E e
      (fun v : Val rT => iprop(∃ x : α, ⌜v = encode x⌝ ∗ ↯ (F x) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (h.wp F hF _) $$ Hcredit
  iintro %x Hcredit
  iexists x
  iframe Hcredit HR
  itrivial

private def zeroBounds : Val rT :=
  ⟨.lam (.pair (.lit (.int 0)) (.lit (.int 0))), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem zero_bounds (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(zeroBounds (rT := rT)).fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (enclosure false n)⌝)) := by
  unfold zeroBounds
  twp_pures
  twp_value
  imodintro
  ipureintro
  rfl

example (E : CoPset) (F : Bool → ℝ≥0∞) (R : IProp GF) :=
  frame (RefinedCoin.refinedCoin_distSpec E (endpoint false) (enclosure false)
    (tight false) (lower_nonneg false) (upper_le false) (fun _ => rfl)
    zeroBounds (zero_bounds E)) F (measurable_of_countable _) R

example (E : CoPset) (R : IProp GF) :=
  frame (RefinedCoin.refinedCoin_distSpec E (endpoint false) (enclosure false)
    (tight false) (lower_nonneg false) (upper_le false) (fun _ => rfl)
    zeroBounds (zero_bounds E)) (fun _ => ∞) measurable_const R

/-- This caller retains the old cache, arbitrary joint credit and an unrelated frame. -/
example (E : CoPset) (p : unitInterval) (a : ℕ → FromBounds.Interval p)
    (ha : FromBounds.Tight a) (hlo : ∀ n, 0 ≤ (a n).lower)
    (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (bounds : Val rT) (index : ℤ)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int index #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a n)⌝)))
    (l : Loc) (q : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (R : IProp GF) :
    iprop(UniformBag.owns l q ∗
      ↯ (LatentBernoulli.credit q (RefinedComparison.threshold p) G) ∗ R) ⊢
      tglWp E pl(&Occil.General.refinedCDFComparison #loc l &bounds.fst #int index)
        (fun v : Val rT => iprop(UniformBag.coinPost l q G v ∗ R)) := by
  iintro ⟨Hbag, Hcredit, HR⟩
  have h := RefinedCDFComparison.refinedCDFComparison_coinSpec E p a ha hlo hhi hden
    bounds index hbounds l
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply h.spec q G hG
    iframe Hbag Hcredit
  iintro %v Hpost
  iframe Hpost HR

private def twice (e : Exp rT) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) e)) e

omit [ProbLangDist.IsUniformInt rT] in
/-- Repeating one threshold on one cache returns the same bit, with joint credit. -/
theorem same_threshold (E : CoPset) (p : unitInterval) (l : Loc) (e : Exp rT)
    (he : e.IsLocallyClosed)
    (hcall : ∀ q G, (∀ b, Measurable (G b)) →
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (RefinedComparison.outputCredit p G))) ⊢
        tglWp E e (RefinedComparison.post l q p G))
    (q : List Bool) (H : Bool → Bool → ℝ → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :
    iprop(UniformBag.owns l q ∗
      ↯ (DyadicPosterior.credit q
        (RefinedComparison.outputCredit p (fun b => H b b))) ∗ R) ⊢
      tglWp E (twice e) (fun v : Val rT => iprop(∃ b r,
        ⌜v = Val.pair (Val.bool b) (Val.bool b) ∧ q <+: r⌝ ∗
        UniformBag.owns l r ∗ ↯ (DyadicPosterior.credit r (H b b)) ∗ R)) := by
  iintro ⟨Hbag, Hcredit, HR⟩
  unfold twice
  twp_bind e
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply hcall q (fun b => RefinedComparison.outputCredit p (H b))
      (fun b => RefinedComparison.measurable_outputCredit p (H b) (hH b))
    have hdiag : RefinedComparison.outputCredit p
        (fun b => RefinedComparison.outputCredit p (H b)) =
        RefinedComparison.outputCredit p (fun b => H b b) := rfl
    isimp only [hdiag]
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [RefinedComparison.post] at Hpost
  ihave ⟨%b, %r, %hr, Hbag, Hcredit⟩ := Hpost
  rcases hr with ⟨rfl, hqr, hbr⟩
  twp_pure
  rw [← Exp.open_lc 0 (Val.bool b).fst e he]
  twp_bind e
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply hcall r (H b) (hH b)
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [RefinedComparison.post] at Hpost
  ihave ⟨%c, %s, %hs, Hbag, Hcredit⟩ := Hpost
  rcases hs with ⟨rfl, hrs, hcs⟩
  have hbs := DyadicPosterior.resolves_refines hrs hbr
  obtain ⟨u, hu, hv⟩ := (hbs.and hcs).exists
  have hbc : b = c := hu.symm.trans hv
  cases hbc
  twp_pures
  twp_value
  imodintro
  iexists b, s
  iframe Hbag Hcredit HR
  ipureintro
  exact ⟨rfl, hqr.trans hrs⟩

example (E : CoPset) (p : unitInterval) (a : ℕ → FromBounds.Interval p)
    (ha : FromBounds.Tight a) (hlo : ∀ n, 0 ≤ (a n).lower)
    (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (bounds : Val rT) (index : ℤ)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int index #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a n)⌝)))
    (l : Loc) (q : List Bool) (H : Bool → Bool → ℝ → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :=
  same_threshold E p l
    pl(&Occil.General.refinedCDFComparison #loc l &bounds.fst #int index) (by is_lc)
    (RefinedCDFComparison.twp_refinedCDFComparison E p a ha hlo hhi hden
      bounds index hbounds l) q H hH R

private def cdfBounds : Val rT :=
  ⟨.lam (.lam (.cond (.binop .lt (.bvar 1) (.lit (.int 3)))
    (.pair (.lit (.int 0)) (.lit (.int 0)))
    (.app (.lam (.pair (.bvar 0) (.bvar 0)))
      (.app (.app Occil.PSRN.integerPower (.lit (.int 2))) (.bvar 0))))),
    .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem cdf_bounds (E : CoPset) (x : ℤ) (n : ℕ) :
    ⊢ tglWp E pl(&(cdfBounds (rT := rT)).fst #int x #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval
        (enclosure (decide (3 ≤ x)) n)⌝)) := by
  unfold cdfBounds
  twp_pures
  by_cases hx : x < 3
  · have htest : decide (x < 3) = true := decide_eq_true hx
    simp only [htest]
    twp_pures
    twp_value
    imodintro
    ipureintro
    have hx' : ¬ 3 ≤ x := by omega
    simp [RefinedComparison.encodeInterval, enclosure, hx']
  · have htest : decide (x < 3) = false := decide_eq_false hx
    simp only [htest]
    twp_pure
    twp_bind pl(&Occil.PSRN.integerPower #2 #int ((n + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply PSRNIntegerPower.twp_integerPower E 2 (n + 1)
    iintro %v %hv
    subst v
    twp_pures
    twp_value
    imodintro
    ipureintro
    have hx' : 3 ≤ x := by omega
    simp [RefinedComparison.encodeInterval, enclosure, hx']

example (E : CoPset) (F : ℤ → ℝ≥0∞) (R : IProp GF) :=
  frame (IncompleteInformation.incompleteInformation_distSpec E cdfModel
    (fun x => enclosure (decide (3 ≤ x))) (fun _ _ => tight _)
    (fun _ _ => lower_nonneg _) (fun _ _ => upper_le _) (fun _ _ _ => rfl)
    cdfBounds (fun x _ => cdf_bounds E x)) F (measurable_of_countable _) R

#print axioms RefinedCoin.refinedCoin_distSpec
#print axioms RefinedCDFComparison.refinedCDFComparison_coinSpec
#print axioms IncompleteInformation.incompleteInformation_distSpec
#print axioms IncompleteInformation.cdf

end callers
end
end ReviewExactStructured004
