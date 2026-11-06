import SampLib.Common.DecreasingTrial
import SampLib.Common.Laws.Exponential
import Metrology.TotalEris.Examples.Samplers.NegExp
import Metrology.Iris.LocalBI

/-! # Von Neumann's exponential sampler

A decreasing chain below `x` has even length with probability `exp (-x)`.
An odd chain discards the fraction and increments the integer part. Thus each
unit strip has density `exp (-(whole + x))`; retries have probability `exp (-1)`.
-/

open Set ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal NNReal

namespace SampLib.Exponential

noncomputable section

open TotalEris.Examples

section mathematics

open MeasureTheory

/-- The standard exponential law with unit rate. -/
def law : Measure ℝ := ProbabilityTheory.expMeasure 1

instance : IsProbabilityMeasure law :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure zero_lt_one

/-- Expected continuation credit over the remaining unit strips. -/
def credit (F : ℝ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  NegExpCreditV (fun k x => F ((k : ℝ) + x)) n

/-- Credits selected by the decreasing chain's parity. -/
def parityCredit (F : ℝ → ℝ≥0∞) (n : ℕ) (x : ℝ) (c : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k % 2 = 0 then F ((n : ℝ) + x) else credit F (n + 1) + c

/-- Expected credit after drawing the proposed fractional part. -/
def drawCredit (F : ℝ → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  DecreasingTrial.credit (parityCredit F n x c) 0 x

theorem measurable_drawCredit (F : ℝ → ℝ≥0∞) (hF : Measurable F) (n : ℕ)
    (c : ℝ≥0∞) : Measurable (drawCredit F n c) :=
  measurable_negExpContAmp (fun k x => F ((k : ℝ) + x))
    (fun _ => hF.comp (measurable_const.add measurable_id)) n c

/-- Parity gives the accepted strip; `exp (-1) * exp 1 = 1` funds retries. -/
theorem expectation_preservation (F : ℝ → ℝ≥0∞) (n : ℕ) (ε : ℝ≥0∞) :
    ∫⁻ x, drawCredit F n ((NegExpFactor : ℝ≥0∞) * ε) x ∂unifUnit =
      credit F n + ε := by
  change (∫⁻ x, RealDecrTrialCreditV
    (NegExpContAmp (fun k x => F ((k : ℝ) + x)) x n
      ((NegExpFactor : ℝ≥0∞) * ε)) 0 x ∂unifUnit) = _
  rw [NegExpCredit_recurrence, ← mul_assoc, NegExpRejectProb_mul_NegExpFactor, one_mul]
  rfl

theorem lintegral_law (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂law = credit F 0 :=
  Distributions.Exponential.lintegral_expMeasure F hF

end mathematics

@[pl_fold] private def loop : Exp ℝ := pl%
  rec draw whole :=
    let x := urand;
    let n := &Occil.decreasingTrial #0 x;
    if n % #2 = #0 then toReal(whole) + x else draw (whole + #1)

private theorem natCast_emod_two (k : ℕ) : (k : ℤ) % 2 = ((k % 2 : ℕ) : ℤ) := by
  omega

theorem exponential_lc {rT : Type _} :
    (Occil.exponential : Exp rT).IsLocallyClosed := by is_lc

theorem exponential_fv {rT : Type _} : (Occil.exponential : Exp rT).fv = ∅ := by
  simp [Occil.exponential, Exp.fv, DecreasingTrial.decreasingTrial_fv]

@[simp] theorem exponential_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.exponential = Occil.exponential :=
  (Exp.open_lc k e _ exponential_lc).symm

@[simp] theorem exponential_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.exponential : Exp rT) = Occil.exponential :=
  Exp.closeRec_fresh x _ k (by simp [exponential_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (n : ℕ) :
    ⊢ ↯ (credit F n) -∗ tglWp E pl(&loop #int (n : ℤ))
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %n Hcredit
  iapply ErrorCredit.Induction.simple hε one_lt_NegExpFactor $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %n Hcredit
  twp_pures
  twp_bind pl(urand)
  icombine Hcredit Hterm as Hcredit
  iapply (twp_urand_exp
    (ε₂ := drawCredit F n ((NegExpFactor : ℝ≥0∞) * ε))
    (measurable_drawCredit F hF n _) ?_) $$ Hcredit
  · rw [expectation_preservation]
  iintro %x ⟨%hx, Hcredit⟩
  have hx' := mem_unifUnitSupport_real.mp hx
  twp_pure
  twp_bind pl(&Occil.decreasingTrial #0 #real x)
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ k : ℕ,
    ⌜v = Val.int k⌝ ∗ ↯ (parityCredit F n x ((NegExpFactor : ℝ≥0∞) * ε) k))))
  isplitl [Hcredit]
  · isimp only [drawCredit] at Hcredit
    iapply (DecreasingTrial.twp_decreasingTrial E
      (parityCredit F n x ((NegExpFactor : ℝ≥0∞) * ε)) 0 x ⟨hx'.1.le, hx'.2.le⟩) $$ Hcredit
  iintro %v ⟨%k, %hv, Hcredit⟩
  subst v
  twp_pures
  obtain hk | hk := Nat.mod_two_eq_zero_or_one k
  · rw [natCast_emod_two, hk]
    twp_pures
    twp_value
    imodintro
    iexists ((n : ℝ) + x)
    isimp only [parityCredit, ite_eq_left hk] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)
  · rw [natCast_emod_two, hk]
    isimp only [parityCredit, hk, Nat.one_ne_zero, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&loop #int ((n + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit

/-- Execute the wrapper around the integer-part loop. -/
theorem twp_exponential (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ z, F z ∂law) -∗ tglWp E pl(&Occil.exponential #())
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  isimp only [lintegral_law F hF] at Hcredit
  twp_pure
  twp_pure
  simp only [DecreasingTrial.decreasingTrial_closeRec, DecreasingTrial.decreasingTrial_openRec]
  change ↯ (credit F 0) ⊢ tglWp E pl(&loop #0)
    (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z)))
  iapply (twp_loop E F hF 0)

/-- Typed standard exponential specification. -/
theorem exponential_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.exponential #()) law Val.real where
  spec F hF := wand_entails (twp_exponential E F hF)

end specification

end

end SampLib.Exponential
