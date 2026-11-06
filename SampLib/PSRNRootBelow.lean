import SampLib.LatentRootModel
import SampLib.PSRNLess
import SampLib.LatentConstantView
import SampLib.PSRNIntegerPower
import SampLib.Syntax.ClosedExp

/-! # The root oracle's exact power-threshold callback

Every callback compares the same source with a constructed rational power. Its
joint continuation credit retains all cache refinements from the source read.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

private instance power_closed {rT : Type} : ClosedExp (Occil.PSRN.integerPower : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.integerPower, Exp.fv]

private instance less_closed {rT : Type} : ClosedExp (Occil.PSRN.less : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.less, Exp.fv]

private instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.PSRN.rational, Exp.fv]

private def belowCode {rT : Type} (source : Exp rT) (degree : ℕ) (denominator : ℤ) : Exp rT :=
  let compare := .app (.app Occil.PSRN.less source)
    (.app (.app Occil.PSRN.rational (.bvar 0)) (.lit (.int (denominator ^ degree))))
  .lam (.app (.lam compare)
    (.app (.app Occil.PSRN.integerPower (.bvar 0)) (.lit (.int (degree : ℤ)))))

private theorem belowCode_lc {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ) :
    (belowCode source.fst degree denominator).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hs (k : ℕ) : Exp.lcb k source.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le k)
  have hp (k : ℕ) : Exp.lcb k (Occil.PSRN.integerPower : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb power_closed.lc) (Nat.zero_le k)
  have hl (k : ℕ) : Exp.lcb k (Occil.PSRN.less : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb less_closed.lc) (Nat.zero_le k)
  have hr (k : ℕ) : Exp.lcb k (Occil.PSRN.rational : Exp rT) = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb rational_closed.lc) (Nat.zero_le k)
  simp [belowCode, Exp.lcb, hs, hp, hl, hr]

/-- The actual callback, after the denominator power has been computed. -/
def belowVal {rT : Type} (source : Val rT) (degree : ℕ) (denominator : ℤ) : Val rT :=
  ⟨belowCode source.fst degree denominator, .lam (belowCode_lc source degree denominator),
    belowCode_lc source degree denominator⟩

variable {Ω S : Type} [MeasurableSpace Ω]

/-- A comparison threshold is another view of the source's joint world. -/
def thresholdModel (D : Model Ω S) (degree : ℕ) (bound denominator : ℤ) : Model Ω S :=
  D.constant (((bound ^ degree : ℤ) : ℝ) / ((denominator ^ degree : ℤ) : ℝ))

private theorem threshold_value (degree : ℕ) (bound denominator : ℤ) :
    (((bound ^ degree : ℤ) : ℝ) / ((denominator ^ degree : ℤ) : ℝ)) =
      ((bound : ℝ) / denominator) ^ degree := by simp [div_pow]

/-- The integer-power rational comparison is exactly the intended real-power threshold. -/
theorem threshold_event_iff (D : Model Ω S) (degree : ℕ) (bound denominator : ℤ) (x : Ω) :
    x ∈ Less.event D (thresholdModel D degree bound denominator) ↔
      D.value x < ((bound : ℝ) / denominator) ^ degree := by
  simp only [Less.event, Set.mem_ofPred_eq, thresholdModel, Model.constant, threshold_value]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Power construction and exact comparison keep the same source-owned joint credit. -/
theorem twp_below (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (degree : ℕ) (bound denominator : ℤ) (hbound : 0 ≤ bound) (hdenominator : 0 < denominator)
    (s : S) (hadmissible : Admissible D degree s)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(P s ∗ ↯ (∫⁻ x, Less.outputCredit D
      (thresholdModel D degree bound denominator) G x ∂D.posterior s)) ⊢
      tglWp E pl(&(belowVal source degree denominator).fst #bound)
        (Less.post D (thresholdModel D degree bound denominator) P s G) := by
  have hpower : 0 < denominator ^ degree := pow_pos hdenominator degree
  have hne : ∀ᵐ x ∂D.posterior s,
      D.value x ≠ (thresholdModel D degree bound denominator).value x := by
    simpa only [thresholdModel, Model.constant, threshold_value] using
      hadmissible.2 bound denominator hbound hdenominator
  iintro ⟨Hstate, Hcredit⟩
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.PSRN.integerPower #bound #int (degree : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply PSRNIntegerPower.twp_integerPower E bound degree
  iintro %power %hpowerVal
  subst power
  twp_pure
  isimp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.PSRN.rational #int (bound ^ degree) #int (denominator ^ degree))
  twp_pures
  rw [decide_eq_false (not_le.mpr hpower)]
  twp_pures
  twp_value
  imodintro
  have hless := Less.twp_less E D (thresholdModel D degree bound denominator)
    (D.sameWorld_constant _) hD (fun _ => measurable_const) P source
    (LatentRational.value (bound ^ degree) (denominator ^ degree)) hsource
    (constant_viewSpec E D P (bound ^ degree) (denominator ^ degree) hpower) s hne G hG
  ieval (
    change _ ⊢ tglWp E pl(&Occil.PSRN.less &source.fst
      &(LatentRational.value (bound ^ degree) (denominator ^ degree)).fst) _)
  iapply hless
  iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.Root
