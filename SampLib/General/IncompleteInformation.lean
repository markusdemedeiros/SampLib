import SampLib.Common.Laws.IncompleteInformation
import SampLib.General.Syntax.IncompleteInformation
import SampLib.General.RefinedCDFComparison

/-! # Finite inverse CDF with progressively refined probabilities

Every bisection compares the same latent uniform. The posterior stays inside the
current quantile bracket, so the final integer has the supplied finite CDF.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.IncompleteInformation

noncomputable section

private theorem equal_test {rT : Type} [BEq rT] (lo hi : ℤ) :
    ((BaseLit.int lo : BaseLit rT) == .int hi) = decide (lo = hi) := by
  change (lo == hi) = decide (lo = hi)
  by_cases h : lo = hi <;> simp [h]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_search (E : CoPset) (D : Model)
    (a : ∀ x : ℤ, ℕ → FromBounds.Interval (D.cdf x))
    (ha : ∀ x, x ∈ Set.Icc 0 D.upper → FromBounds.Tight (a x))
    (hlo : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n, 0 ≤ (a x n).lower)
    (hhi : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n, (a x n).upper ≤ (a x n).denominator)
    (hden : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n,
      (a x n).denominator = 2 ^ (n + 1)) (bounds : Val rT)
    (hbounds : ∀ x : ℤ, x ∈ Set.Icc 0 D.upper → ∀ n : ℕ,
      ⊢ tglWp E pl(&bounds.fst #int x #int ((n + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a x n)⌝)))
    (l : Loc) (lo hi : ℤ) (q : List Bool) (hbracket : Bracket D q lo hi)
    (F : ℤ → ℝ≥0∞) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (fun u => F (quantile D u)))) ⊢
      tglWp E pl(&(Program.search bounds l) #int lo #int hi)
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  have hall : ∀ width : ℕ, ∀ lo hi q, (hi - lo).toNat = width → Bracket D q lo hi →
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (fun u => F (quantile D u)))) ⊢
        tglWp E pl(&(Program.search bounds l) #int lo #int hi)
          (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
    intro width
    induction width using Nat.strong_induction_on with
    | h width IH =>
      intro lo hi q hwidth hbracket
      iintro ⟨Hbag, Hcredit⟩
      twp_pures
      simp only [Program.comparison_openRec]
      rw [equal_test]
      by_cases heq : lo = hi
      · simp only [heq, decide_true]
        twp_pures
        twp_value
        imodintro
        iexists hi
        subst lo
        isimp only [Bracket.done_credit hbracket F] at Hcredit
        iframe Hcredit
        itrivial
      · have hlt : lo < hi := lt_of_le_of_ne hbracket.2.2.1 heq
        simp only [decide_eq_false heq]
        iterate 4 twp_pure
        simp only [Program.comparison_openRec]
        let mid := (lo + hi) / 2
        have hmid := Bracket.midpoint_mem hbracket hlt
        twp_bind pl(&Occil.General.refinedCDFComparison #loc l &bounds.fst #int mid)
        iapply tglWp_wand
        isplitl [Hbag Hcredit]
        · iapply RefinedCDFComparison.twp_refinedCDFComparison E (D.cdf mid)
            (a mid) (ha mid hmid) (hlo mid hmid) (hhi mid hmid) (hden mid hmid) bounds mid
            (hbounds mid hmid) l q (fun _ u => F (quantile D u))
            (fun _ => (measurable_of_countable F).comp (measurable_quantile D))
          rw [RefinedComparison.outputCredit_ignore_result]
          iframe Hbag Hcredit
        iintro %v Hpost
        isimp only [RefinedComparison.post] at Hpost
        ihave ⟨%b, %r, %hr, Hbag, Hcredit⟩ := Hpost
        rcases hr with ⟨rfl, hqr, hcmp⟩
        have hrange := Bracket.refines hbracket hqr
        cases b
        · iterate 2 twp_pure
          have hright := Bracket.right hrange hlt hcmp
          have hsmaller := Bracket.right_width lo hi hlt
          rw [hwidth] at hsmaller
          twp_bind pl(&(Program.search bounds l) #int (mid + 1) #int hi)
          iapply (tglWp_mono fun _ => tglWp_value)
          iapply IH _ hsmaller (mid + 1) hi r rfl hright
          iframe Hbag Hcredit
        · twp_pure
          have hleft := Bracket.left hrange hlt hcmp
          have hsmaller := Bracket.left_width lo hi hlt
          rw [hwidth] at hsmaller
          twp_bind pl(&(Program.search bounds l) #int lo #int mid)
          iapply (tglWp_mono fun _ => tglWp_value)
          iapply IH _ hsmaller lo mid r rfl hleft
          iframe Hbag Hcredit
  exact hall _ lo hi q rfl hbracket

/-- Exact finite CDF sampling, including irrational masses and zero-probability outcomes. -/
theorem twp_incompleteInformation (E : CoPset) (D : Model)
    (a : ∀ x : ℤ, ℕ → FromBounds.Interval (D.cdf x))
    (ha : ∀ x, x ∈ Set.Icc 0 D.upper → FromBounds.Tight (a x))
    (hlo : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n, 0 ≤ (a x n).lower)
    (hhi : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n, (a x n).upper ≤ (a x n).denominator)
    (hden : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n,
      (a x n).denominator = 2 ^ (n + 1)) (bounds : Val rT)
    (hbounds : ∀ x : ℤ, x ∈ Set.Icc 0 D.upper → ∀ n : ℕ,
      ⊢ tglWp E pl(&bounds.fst #int x #int ((n + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a x n)⌝))) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law D) -∗
      tglWp E pl(&Occil.General.incompleteInformation #int (D.size : ℤ) &bounds.fst #())
        (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  isimp only [← expectation D F] at Hcredit
  iapply Program.twp_open E D.size D.positive bounds _
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  iapply Program.twp_open_bag E (D.size : ℤ) bounds l _
  have hsearch := twp_search E D a ha hlo hhi hden bounds hbounds l 0 D.upper []
    (Bracket.initial D []) F
  simp only [Model.upper] at hsearch
  iapply hsearch
  iframe Hbag Hcredit

/-- The returned integer has the supplied normalized finite CDF. -/
theorem incompleteInformation_distSpec (E : CoPset) (D : Model)
    (a : ∀ x : ℤ, ℕ → FromBounds.Interval (D.cdf x))
    (ha : ∀ x, x ∈ Set.Icc 0 D.upper → FromBounds.Tight (a x))
    (hlo : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n, 0 ≤ (a x n).lower)
    (hhi : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n, (a x n).upper ≤ (a x n).denominator)
    (hden : ∀ x, x ∈ Set.Icc 0 D.upper → ∀ n,
      (a x n).denominator = 2 ^ (n + 1)) (bounds : Val rT)
    (hbounds : ∀ x : ℤ, x ∈ Set.Icc 0 D.upper → ∀ n : ℕ,
      ⊢ tglWp E pl(&bounds.fst #int x #int ((n + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(⌜v = RefinedComparison.encodeInterval (a x n)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.incompleteInformation #int (D.size : ℤ) &bounds.fst #())
      (law D) Val.int where
  spec F _ := wand_entails (twp_incompleteInformation E D a ha hlo hhi hden bounds hbounds F)

end specification

end

end SampLib.IncompleteInformation
