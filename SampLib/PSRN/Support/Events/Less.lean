import SampLib.Latent.LatentViews
import SampLib.PSRN.Laws.LessKernel
import SampLib.PSRN.Syntax.PSRNLess
import SampLib.PSRN.Support.Events.EventSpec

/-! # Exact comparison of shared lazy-real views

The two reads consume and return one common ownership predicate. A fixed finite
uncertainty horizon proves termination for almost-surely distinct latent values.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Less

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A resolved event retains the physical world and its whole joint posterior credit. -/
def post (Dleft Dright : Model Ω S) (P : S → IProp GF) (initial : S)
    (G : Bool → Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ (b : Bool) (t : S),
    ⌜result = Val.bool b ∧ Dleft.refines initial t ∧
      ∀ᵐ x ∂Dleft.posterior t, decide (x ∈ event Dleft Dright) = b⌝ ∗
    P t ∗ ↯ (∫⁻ x, G b x ∂Dleft.posterior t))

private theorem twp_round (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (hl : Dleft.MeasurableError) (hr : Dright.MeasurableError)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right)
    (initial s : S) (hs : Dleft.refines initial s) (N n : ℕ)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b))
    (hcontinue : ∀ (t : S) (I J : RationalInterval), Dleft.refines s t →
      Dleft.Encloses t n I → Dright.Encloses t n J →
      (¬I.upper * J.denominator < J.lower * I.denominator) →
      (¬J.upper * I.denominator ≤ I.lower * J.denominator) →
      iprop(P t ∗ ↯ (∫⁻ x, horizonCredit Dleft Dright N G x ∂Dleft.posterior t)) ⊢
        tglWp E pl(&(Program.loop left right) #int ((n + 1 : ℕ) : ℤ))
          (post Dleft Dright P initial G)) :
    iprop(P s ∗ ↯ (∫⁻ x, horizonCredit Dleft Dright N G x ∂Dleft.posterior s)) ⊢
      tglWp E pl(&(Program.loop left right) #int (n : ℤ))
        (post Dleft Dright P initial G) := by
  iintro ⟨Hstate, Hcredit⟩
  iterate 2 twp_pure
  twp_bind pl(&left.fst #int (n : ℤ))
  iapply hleft.wp s n (horizonCredit Dleft Dright N G)
    (measurable_horizonCredit Dleft Dright hl hr N G hG) _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  twp_pure
  twp_bind pl(&right.fst #int (n : ℤ))
  isimp only [← hworld.posterior_eq t] at Hcredit
  iapply hright.wp t n (horizonCredit Dleft Dright N G)
    (measurable_horizonCredit Dleft Dright hl hr N G hG) _ $$ Hstate Hcredit
  iintro %u %J %hJ Hstate Hcredit
  isimp only [hworld.posterior_eq u] at Hcredit
  have htu := (hworld.refines_iff t u).mp hJ.1
  have hsu := Dleft.refines_trans hI.1 htu
  have hI' := Dleft.encloses_refines htu hI.2
  iterate 12 twp_pure
  by_cases hstrict : I.upper * J.denominator < J.lower * I.denominator
  · rw [decide_eq_true hstrict]
    twp_pure
    twp_value
    imodintro
    isimp only [post]
    iexists true, u
    have hresolve := true_resolves Dleft Dright hworld hI' hJ.2 hstrict
    ihave Hcredit := ErrorCredit.weaken
      (return_credit Dleft Dright u N G true hresolve) $$ Hcredit
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, Dleft.refines_trans hs hsu, hresolve⟩
  · rw [decide_eq_false hstrict]
    iterate 8 twp_pure
    by_cases hreverse : J.upper * I.denominator ≤ I.lower * J.denominator
    · rw [decide_eq_true hreverse]
      twp_pure
      twp_value
      imodintro
      isimp only [post]
      iexists false, u
      have hresolve := false_resolves Dleft Dright hworld hI' hJ.2 hreverse
      ihave Hcredit := ErrorCredit.weaken
        (return_credit Dleft Dright u N G false hresolve) $$ Hcredit
      iframe Hstate Hcredit
      ipureintro
      exact ⟨rfl, Dleft.refines_trans hs hsu, hresolve⟩
    · rw [decide_eq_false hreverse]
      iterate 2 twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&(Program.loop left right) #int ((n + 1 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply hcontinue u I J hsu hI' hJ.2 hstrict hreverse
      iframe Hstate Hcredit

private theorem twp_until (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (hl : Dleft.MeasurableError) (hr : Dright.MeasurableError)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right)
    (initial s : S) (hs : Dleft.refines initial s) (N n : ℕ) (hn : n ≤ N)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(P s ∗ ↯ (∫⁻ x, horizonCredit Dleft Dright N G x ∂Dleft.posterior s)) ⊢
      tglWp E pl(&(Program.loop left right) #int (n : ℤ))
        (post Dleft Dright P initial G) := by
  have hall : ∀ n ≤ N, ∀ s, Dleft.refines initial s →
      iprop(P s ∗ ↯ (∫⁻ x, horizonCredit Dleft Dright N G x ∂Dleft.posterior s)) ⊢
        tglWp E pl(&(Program.loop left right) #int (n : ℤ))
          (post Dleft Dright P initial G) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ s, Dleft.refines initial s →
      iprop(P s ∗ ↯ (∫⁻ x, horizonCredit Dleft Dright N G x ∂Dleft.posterior s)) ⊢
        tglWp E pl(&(Program.loop left right) #int (n : ℤ))
          (post Dleft Dright P initial G)) ?_ ?_ hn
    · intro n hn IH s hs
      iapply twp_round E Dleft Dright hworld hl hr P left right hleft hright
        initial s hs N n G hG (fun t _ _ hst _ _ _ _ => IH t (Dleft.refines_trans hs hst))
    · intro s hs
      iapply twp_round E Dleft Dright hworld hl hr P left right hleft hright
        initial s hs N N G hG ?_
      intro t I J hst hI hJ hstrict hreverse
      iintro ⟨Hstate, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict
        (unresolved_credit Dleft Dright hworld t N G I J hI hJ hstrict hreverse) $$ Hcredit
  exact hall n hn s hs

/-- Exact shared-world comparison for almost-surely unequal values; no independence is assumed. -/
theorem twp_less (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (hl : Dleft.MeasurableError) (hr : Dright.MeasurableError)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right)
    (s : S) (hne : ∀ᵐ x ∂Dleft.posterior s, Dleft.value x ≠ Dright.value x)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(P s ∗ ↯ (∫⁻ x, outputCredit Dleft Dright G x ∂Dleft.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.less &left.fst &right.fst) (post Dleft Dright P s G) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply Program.twp_open E left right _
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN, hcost⟩ := exists_horizon Dleft Dright hworld hl hr s hne 1 G hG δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hcost $$ Htotal
  iapply twp_until E Dleft Dright hworld hl hr P left right hleft hright
    s s (Dleft.refines_refl s) N 1 hN G hG
  iframe Hstate Hcredit

/-- The termination domain is a pure property of the current posterior, retained by refinement. -/
def distinctState (Dleft Dright : Model Ω S) (P : S → IProp GF) (s : S) : IProp GF :=
  iprop(⌜∀ᵐ x ∂Dleft.posterior s, Dleft.value x ≠ Dright.value x⌝ ∗ P s)

/-- A reusable event callback with state-local separation and one shared physical ownership. -/
theorem less_eventSpec (E : CoPset) (Dleft Dright : Model Ω S)
    (hworld : Dleft.SameWorld Dright) (hl : Dleft.MeasurableError) (hr : Dright.MeasurableError)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right) :
    IsEventSpec E Dleft (ViewOwns left (distinctState Dleft Dright P))
      (event Dleft Dright) (Program.acceptValue right) where
  measurable_event := measurableSet_event Dleft Dright
  spec source s G hG := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, distinctState] at Hstate
    icases Hstate with ⟨%hsource, %hne, Hstate⟩
    subst source
    iapply Program.twp_open_accept E left right _
    have hstep := twp_less E Dleft Dright hworld hl hr P left right hleft hright s hne G hG
    simp only [outputCredit] at hstep
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply hstep
      iframe Hstate Hcredit
    iintro %result Hpost
    isimp only [post] at Hpost
    ihave ⟨%b, %t, %ht, Hstate, Hcredit⟩ := Hpost
    iexists b, t
    isplit
    · ipureintro
      exact ht
    isplitl [Hstate]
    · isimp only [ViewOwns, distinctState]
      isplit
      · itrivial
      isplit
      · ipureintro
        exact (Dleft.absolutelyContinuous ht.2.1).ae_le hne
      · iframe Hstate
    · iframe Hcredit

end

end SampLib.LatentReal.Less
