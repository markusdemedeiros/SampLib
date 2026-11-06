import SampLib.PSRNRootBelow
import SampLib.Distributions.LatentReal.RootKernel
import SampLib.Syntax.PSRNRootLoops

/-! # The root oracle's expanding upper bracket

Only one tail band funds the search. Every callback refines the same owned source;
a failed comparison at the selected finite horizon contradicts its whole credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

section mathematics

open MeasureTheory

variable {Ω S : Type} [MeasurableSpace Ω]

private theorem double_bound (denominator : ℤ) (k : ℕ) :
    denominator * 2 ^ k * 2 = denominator * 2 ^ (k + 1) := by ring

private theorem divided_bound (denominator : ℤ) (hdenominator : 0 < denominator) (k : ℕ) :
    (((denominator * 2 ^ k : ℤ) : ℝ) / denominator) = (2 : ℝ) ^ k := by
  push_cast
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hdenominator.ne')

private theorem bracket_return_credit (D : Model Ω S) (s : S) (N : ℕ) (F : Ω → ℝ≥0∞) :
    (∫⁻ x, F x ∂D.posterior s) ≤ ∫⁻ x, horizonCredit D N F x ∂D.posterior s :=
  lintegral_mono fun _ => le_add_right le_rfl

private theorem bracket_unresolved_credit (D : Model Ω S) (s : S) (degree N : ℕ)
    (hdegree : degree ≠ 0) (denominator : ℤ) (hdenominator : 0 < denominator)
    (F : Ω → ℝ≥0∞)
    (hresolve : ∀ᵐ x ∂D.posterior s,
      decide (x ∈ Less.event D (thresholdModel D degree (denominator * 2 ^ N) denominator)) =
        false) :
    1 ≤ ∫⁻ x, horizonCredit D N F x ∂D.posterior s := by
  calc
    1 = ∫⁻ _ : Ω, 1 ∂D.posterior s := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hresolve] with x hx
      have hbound : ((2 : ℝ) ^ N) ^ degree ≤ D.value x := by
        simpa only [threshold_event_iff, divided_bound denominator hdenominator N,
          decide_eq_false_iff_not, not_lt] using hx
      have hband := unresolved_mem_tailBand D degree N hdegree x hbound
      simp [horizonCredit, hband]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A discovered positive upper bound retains its actual source and joint output credit. -/
def bracketPost (D : Model Ω S) (P : S → IProp GF) (initial : S)
    (degree : ℕ) (denominator : ℤ) (F : Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ (hi : ℤ) (t : S),
    ⌜result = Val.int hi ∧ 0 < hi ∧ D.refines initial t ∧
      ∀ᵐ x ∂D.posterior t, D.value x < ((hi : ℝ) / denominator) ^ degree⌝ ∗
    P t ∗ ↯ (∫⁻ x, F x ∂D.posterior t))

private theorem twp_bracket_round (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (denominator : ℤ) (hdenominator : 0 < denominator)
    (initial s : S) (hs : D.refines initial s) (hadmissible : Admissible D degree initial)
    (N k : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hcontinue : ∀ t : S, D.refines s t →
      (∀ᵐ x ∂D.posterior t,
        decide (x ∈ Less.event D (thresholdModel D degree (denominator * 2 ^ k) denominator)) =
          false) →
      iprop(P t ∗ ↯ (∫⁻ x, horizonCredit D N F x ∂D.posterior t)) ⊢
        tglWp E pl(&(Program.bracket (belowVal source degree denominator))
          #int (denominator * 2 ^ (k + 1))) (bracketPost D P initial degree denominator F)) :
    iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D N F x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.bracket (belowVal source degree denominator))
        #int (denominator * 2 ^ k)) (bracketPost D P initial degree denominator F) := by
  iintro ⟨Hstate, Hcredit⟩
  iterate 2 twp_pure
  twp_bind pl(&(belowVal source degree denominator).fst #int (denominator * 2 ^ k))
  have hquery := twp_below E D hD P source hsource degree (denominator * 2 ^ k) denominator
    (by positivity) hdenominator s (hadmissible.refines hs)
    (fun _ => horizonCredit D N F) (fun _ => measurable_horizonCredit D N F hF)
  simp only [Less.outputCredit] at hquery
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply hquery
    iframe Hstate Hcredit
  iintro %result Hpost
  isimp only [Less.post] at Hpost
  icases Hpost with ⟨%b, %t, %ht, Hstate, Hcredit⟩
  rcases ht with ⟨rfl, hst, hresolve⟩
  cases b
  · iterate 2 twp_pure
    rw [double_bound]
    twp_bind pl(&(Program.bracket (belowVal source degree denominator))
      #int (denominator * 2 ^ (k + 1)))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply hcontinue t hst hresolve
    iframe Hstate Hcredit
  · twp_pure
    twp_value
    imodintro
    isimp only [bracketPost]
    iexists denominator * 2 ^ k, t
    ihave Hcredit := ErrorCredit.weaken (bracket_return_credit D t N F) $$ Hcredit
    iframe Hstate Hcredit
    ipureintro
    refine ⟨rfl, by positivity, D.refines_trans hs hst, ?_⟩
    simpa only [threshold_event_iff, decide_eq_true_eq] using hresolve

private theorem twp_bracket_until (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (hdegree : degree ≠ 0) (denominator : ℤ) (hdenominator : 0 < denominator)
    (initial s : S) (hs : D.refines initial s) (hadmissible : Admissible D degree initial)
    (N k : ℕ) (hk : k ≤ N) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D N F x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.bracket (belowVal source degree denominator))
        #int (denominator * 2 ^ k)) (bracketPost D P initial degree denominator F) := by
  have hall : ∀ k ≤ N, ∀ s, D.refines initial s →
      iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D N F x ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.bracket (belowVal source degree denominator))
          #int (denominator * 2 ^ k)) (bracketPost D P initial degree denominator F) := by
    intro k hk
    apply Nat.decreasingInduction (motive := fun k _ => ∀ s, D.refines initial s →
      iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D N F x ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.bracket (belowVal source degree denominator))
          #int (denominator * 2 ^ k)) (bracketPost D P initial degree denominator F)) ?_ ?_ hk
    · intro k hk IH s hs
      iapply twp_bracket_round E D hD P source hsource degree denominator hdenominator
        initial s hs hadmissible N k F hF
        (fun t hst _ => IH t (D.refines_trans hs hst))
    · intro s hs
      iapply twp_bracket_round E D hD P source hsource degree denominator hdenominator
        initial s hs hadmissible N N F hF ?_
      intro t hst hresolve
      iintro ⟨Hstate, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict
        (bracket_unresolved_credit D t degree N hdegree denominator hdenominator F hresolve)
        $$ Hcredit
  exact hall k hk s hs

/-- The actual doubling loop terminates while preserving the same source cache. -/
theorem twp_bracket (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (hdegree : degree ≠ 0) (denominator : ℤ) (hdenominator : 0 < denominator)
    (s : S) (hadmissible : Admissible D degree s) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.bracket (belowVal source degree denominator)) #denominator)
        (bracketPost D P s degree denominator F) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN, hcost⟩ := exists_horizon D s 0 F hF δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hcost $$ Htotal
  have hstart := twp_bracket_until E D hD P source hsource degree hdegree denominator
    hdenominator s s (D.refines_refl s) hadmissible N 0 hN F hF
  simp only [pow_zero, mul_one] at hstart
  iapply hstart
  iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.Root
