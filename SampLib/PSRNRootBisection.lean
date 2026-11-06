import SampLib.PSRNRootBelow
import SampLib.Syntax.PSRNRootLoops

/-! # Finite integer bisection for the deferred root oracle

The integer gap strictly decreases. Each exact threshold callback preserves the
same owned posterior and the mathematical lower/upper power bracket.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The source remains between the powers of two nonnegative rational endpoints. -/
def Bracketed (D : Model Ω S) (degree : ℕ) (denominator lo hi : ℤ) (s : S) : Prop :=
  ∀ᵐ x ∂D.posterior s,
    ((lo : ℝ) / denominator) ^ degree ≤ D.value x ∧
      D.value x < ((hi : ℝ) / denominator) ^ degree

namespace Bracketed

theorem refines {D : Model Ω S} {degree : ℕ} {denominator lo hi : ℤ} {s t : S}
    (h : Bracketed D degree denominator lo hi s) (hst : D.refines s t) :
    Bracketed D degree denominator lo hi t := (D.absolutelyContinuous hst).ae_le h

theorem upper {D : Model Ω S} {degree : ℕ} {denominator lo mid hi : ℤ} {s : S}
    (h : Bracketed D degree denominator lo hi s)
    (hresolve : ∀ᵐ x ∂D.posterior s,
      decide (x ∈ Less.event D (thresholdModel D degree mid denominator)) = true) :
    Bracketed D degree denominator lo mid s := by
  filter_upwards [h, hresolve] with x hx hm
  refine ⟨hx.1, ?_⟩
  simpa only [threshold_event_iff, decide_eq_true_eq] using hm

theorem lower {D : Model Ω S} {degree : ℕ} {denominator lo mid hi : ℤ} {s : S}
    (h : Bracketed D degree denominator lo hi s)
    (hresolve : ∀ᵐ x ∂D.posterior s,
      decide (x ∈ Less.event D (thresholdModel D degree mid denominator)) = false) :
    Bracketed D degree denominator mid hi s := by
  filter_upwards [h, hresolve] with x hx hm
  refine ⟨?_, hx.2⟩
  simpa only [threshold_event_iff, decide_eq_false_iff_not, not_lt] using hm

theorem ne {D : Model Ω S} {degree : ℕ} {denominator lo hi : ℤ} {s : S}
    (h : Bracketed D degree denominator lo hi s) : lo ≠ hi := by
  intro heq
  subst hi
  obtain ⟨x, hx⟩ := h.exists
  exact hx.2.not_ge hx.1

theorem adjacent {D : Model Ω S} {degree : ℕ} {denominator lo hi : ℤ} {s : S}
    (h : Bracketed D degree denominator lo hi s) (hordered : lo ≤ hi) (hstop : hi - lo ≤ 1) :
    hi = lo + 1 := by
  have hne := h.ne
  omega

theorem contains {D : Model Ω S} {degree : ℕ} {denominator lo hi : ℤ} {s : S}
    (h : Bracketed D degree denominator lo hi s) (hdegree : degree ≠ 0)
    (hdenominator : 0 < denominator) (hlo : 0 ≤ lo) (hordered : lo ≤ hi)
    (hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x) :
    ∀ᵐ x ∂D.posterior s,
      (⟨lo, hi, denominator, hdenominator, hordered⟩ : RationalInterval).Contains
        (root degree (D.value x)) := by
  filter_upwards [h, hnonneg] with x hx hnonneg
  apply RationalInterval.contains_root _ hdegree hnonneg
  · exact div_nonneg (by exact_mod_cast hlo) (by exact_mod_cast hdenominator.le)
  · exact hx.1
  · exact hx.2.le

/-- The strict upper bracket identifies the exact floor cell, including its endpoint convention. -/
theorem floor {D : Model Ω S} {degree : ℕ} {denominator lo hi : ℤ} {s : S}
    (h : Bracketed D degree denominator lo hi s) (hdegree : degree ≠ 0)
    (hdenominator : 0 < denominator) (hlo : 0 ≤ lo) (hordered : lo ≤ hi) (hstop : hi - lo ≤ 1)
    (hnonneg : ∀ᵐ x ∂D.posterior s, 0 ≤ D.value x) :
    ∀ᵐ x ∂D.posterior s, ⌊root degree (D.value x) * denominator⌋ = lo := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast hdenominator
  have hgap := h.adjacent hordered hstop
  filter_upwards [h, hnonneg, h.contains hdegree hdenominator hlo hordered hnonneg]
    with x hx hn hc
  have hu : root degree (D.value x) < (hi : ℝ) / denominator :=
    (below_root_iff hdegree hn (div_nonneg
      (by exact_mod_cast hlo.trans hordered) hd.le)).mp hx.2
  apply Int.floor_eq_iff.mpr
  refine ⟨(div_le_iff₀ hd).mp hc.1, ?_⟩
  simpa only [hgap, Int.cast_add, Int.cast_one] using (lt_div_iff₀ hd).mp hu

end Bracketed

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The final enclosure preserves the source and is at most one denominator unit wide. -/
def bisectPost (D : Model Ω S) (P : S → IProp GF) (initial : S)
    (degree : ℕ) (denominator : ℤ) (F : Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ (t : S) (I : RationalInterval),
    ⌜result = intervalVal I ∧ D.refines initial t ∧
      (∀ᵐ x ∂D.posterior t, I.Contains (root degree (D.value x))) ∧
      I.width ≤ 1 / (denominator : ℝ) ∧ I.denominator = denominator ∧
      I.upper = I.lower + 1 ∧
      (∀ᵐ x ∂D.posterior t, ⌊root degree (D.value x) * denominator⌋ = I.lower)⌝ ∗
      P t ∗ ↯ (∫⁻ x, F x ∂D.posterior t))

/-- The actual binary search terminates because each recursive call shortens its integer gap. -/
theorem twp_bisect (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (hdegree : degree ≠ 0) (denominator : ℤ) (hdenominator : 0 < denominator)
    (initial s : S) (hs : D.refines initial s) (hadmissible : Admissible D degree initial)
    (lo hi : ℤ) (hlo : 0 ≤ lo) (hordered : lo ≤ hi)
    (hbounded : Bracketed D degree denominator lo hi s)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    iprop(P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.bisect (belowVal source degree denominator) denominator) #lo #hi)
        (bisectPost D P initial degree denominator F) := by
  have hall : ∀ gap : ℕ, ∀ lo hi : ℤ, (hi - lo).toNat = gap → 0 ≤ lo → lo ≤ hi →
      ∀ s : S, D.refines initial s → Bracketed D degree denominator lo hi s →
      iprop(P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.bisect (belowVal source degree denominator) denominator) #lo #hi)
          (bisectPost D P initial degree denominator F) := by
    intro gap
    induction gap using Nat.strong_induction_on with
    | h gap IH =>
      intro lo hi hgap hlo hordered s hs hbounded
      iintro ⟨Hstate, Hcredit⟩
      iterate 5 twp_pure
      by_cases hstop : hi - lo ≤ 1
      · rw [decide_eq_true hstop]
        twp_pure
        twp_value
        imodintro
        isimp only [bisectPost]
        let I : RationalInterval := ⟨lo, hi, denominator, hdenominator, hordered⟩
        iexists s, I
        iframe Hstate Hcredit
        ipureintro
        exact ⟨rfl, hs,
          hbounded.contains hdegree hdenominator hlo hordered (hadmissible.refines hs).1,
          I.width_le_inv_denominator hstop, rfl, hbounded.adjacent hordered hstop,
          hbounded.floor hdegree hdenominator hlo hordered hstop (hadmissible.refines hs).1⟩
      · rw [decide_eq_false hstop]
        iterate 4 twp_pure
        let mid : ℤ := (lo + hi) / 2
        have hmid : lo < mid ∧ mid < hi := by dsimp [mid]; omega
        twp_bind pl(&(belowVal source degree denominator).fst #int mid)
        have hquery := twp_below E D hD P source hsource degree mid denominator
          (by omega) hdenominator s (hadmissible.refines hs) (fun _ => F) (fun _ => hF)
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
        · twp_pure
          twp_bind pl(&(Program.bisect (belowVal source degree denominator) denominator) #mid #hi)
          iapply (tglWp_mono fun _ => tglWp_value)
          iapply IH (hi - mid).toNat (by omega) mid hi rfl (by omega) (by omega) t
            (D.refines_trans hs hst) ((hbounded.refines hst).lower hresolve)
          iframe Hstate Hcredit
        · twp_pure
          twp_bind pl(&(Program.bisect (belowVal source degree denominator) denominator) #lo #mid)
          iapply (tglWp_mono fun _ => tglWp_value)
          iapply IH (mid - lo).toNat (by omega) lo mid rfl hlo (by omega) t
            (D.refines_trans hs hst) ((hbounded.refines hst).upper hresolve)
          iframe Hstate Hcredit
  exact hall (hi - lo).toNat lo hi rfl hlo hordered s hs hbounded

end specification

end

end SampLib.LatentReal.Root
