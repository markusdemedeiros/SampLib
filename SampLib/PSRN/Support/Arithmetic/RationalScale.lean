import SampLib.PSRN.Support.Arithmetic.RealMap

/-! # Rational scaling of a deferred real

The source posterior and all shared latent dependencies are retained. A negative
scale swaps the enclosure endpoints; the error is multiplied by its absolute value.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

private theorem scaled_interval_width (I : RationalInterval) (a b : ℤ) (hb : 0 < b) :
    (I.scaleRational a b hb).width = I.width * |(a : ℝ) / b| := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  by_cases ha : a < 0
  · have hq : (a : ℝ) / b ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha.le) hb'.le
    simp only [RationalInterval.width, RationalInterval.lowerReal_scaleRational,
      RationalInterval.upperReal_scaleRational, ite_eq_left ha, abs_of_nonpos hq]
    ring
  · have hq : (0 : ℝ) ≤ a / b := div_nonneg (by exact_mod_cast le_of_not_gt ha) hb'.le
    simp only [RationalInterval.width, RationalInterval.lowerReal_scaleRational,
      RationalInterval.upperReal_scaleRational, ite_eq_right ha, abs_of_nonneg hq]
    ring

/-- Interval scaling transports the same posterior enclosure and its error bound. -/
theorem encloses_scaleRational (D : Model Ω S) {s : S} {n : ℕ} {I : RationalInterval}
    (hI : D.Encloses s n I) (a b : ℤ) (hb : 0 < b) :
    (D.scale ((a : ℝ) / b)).Encloses s n (I.scaleRational a b hb) := by
  exact hI.mono fun x hx => ⟨I.contains_scaleRational a b hb hx.1, by
    change (I.scaleRational a b hb).width ≤ D.error n x * |(a : ℝ) / b|
    rw [scaled_interval_width]
    exact mul_le_mul_of_nonneg_right hx.2 (abs_nonneg _)⟩

end Model

private def scaleRationalCode {rT : Type} (source : Exp rT) (a b : ℤ) : Exp rT :=
  let lower := Exp.binop .mult (.fst (.bvar 1)) (.lit (.int a))
  let upper := Exp.binop .mult (.fst (.bvar 0)) (.lit (.int a))
  let denominator := Exp.binop .mult (.snd (.bvar 0)) (.lit (.int b))
  .lam (.app (.lam (.app (.lam
    (.cond (.binop .lt (.lit (.int a)) (.lit (.int 0)))
      (.pair upper (.pair lower denominator)) (.pair lower (.pair upper denominator))))
    (.snd (.bvar 0)))) (.app source (.bvar 0)))

/-- The actual scaled-oracle closure, with source insertion after binder construction. -/
def scaleRationalVal {rT : Type} (source : Val rT) (a b : ℤ) : Val rT :=
  ⟨scaleRationalCode source.fst a b, .lam (by
    apply Exp.lcb_imp_lc
    have hs (n : ℕ) : Exp.lcb n source.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le n)
    simp [Exp.lcb, hs]), by
    apply Exp.lcb_imp_lc
    have hs (n : ℕ) : Exp.lcb n source.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le n)
    simp [scaleRationalCode, Exp.lcb, hs]⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Scaling retains precisely the physical source state. -/
def scaleRationalOwns (owns : Val rT → S → IProp GF) (a b : ℤ)
    (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ source : Val rT, ⌜v = scaleRationalVal source a b⌝ ∗ owns source s)

/-- Constructing the scaled closure performs no source observation. -/
theorem twp_scaleRational (E : CoPset) (owns : Val rT → S → IProp GF)
    (source : Val rT) (s : S) (a b : ℤ) (hb : 0 < b) :
    iprop(owns source s) ⊢
      tglWp E pl(&Occil.PSRN.scaleRational &source.fst #a #b)
        (fun v => scaleRationalOwns owns a b v s) := by
  iintro Hstate
  twp_pures
  rw [decide_eq_false (not_le.mpr hb)]
  twp_pures
  twp_value
  imodintro
  isimp only [scaleRationalOwns]
  iexists source
  iframe Hstate
  ipureintro
  apply Val.ext
  simp [scaleRationalVal, scaleRationalCode]

/-- Every scaled read preserves arbitrary credit on the entire joint latent space. -/
theorem scaleRational_oracleSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D owns)
    (a b : ℤ) (hb : 0 < b) :
    IsOracleSpec E (D.scale ((a : ℝ) / b)) (scaleRationalOwns owns a b) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [scaleRationalOwns] at Hstate
    icases Hstate with ⟨%source, %hsourceVal, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&source.fst #int (n : ℤ))
    isimp only [Model.scale] at Hcredit
    iapply hsource.wp source s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    by_cases ha : a < 0
    · rw [decide_eq_true ha]
      twp_pures
      twp_value
      imodintro
      iexists t, I.scaleRational a b hb
      isplit
      · ipureintro
        refine ⟨?_, hI.1, D.encloses_scaleRational hI.2 a b hb⟩
        apply Val.ext
        simp [intervalVal, RationalInterval.scaleRational, ha, Exp.ofVal]
      isplitl [Hstate]
      · isimp only [scaleRationalOwns]
        iexists source
        iframe Hstate
        itrivial
      isimp only [Model.scale]
      iframe Hcredit
    · rw [decide_eq_false ha]
      twp_pures
      twp_value
      imodintro
      iexists t, I.scaleRational a b hb
      isplit
      · ipureintro
        refine ⟨?_, hI.1, D.encloses_scaleRational hI.2 a b hb⟩
        apply Val.ext
        simp [intervalVal, RationalInterval.scaleRational, ha, Exp.ofVal]
      isplitl [Hstate]
      · isimp only [scaleRationalOwns]
        iexists source
        iframe Hstate
        itrivial
      isimp only [Model.scale]
      iframe Hcredit

end specification

end

end SampLib.LatentReal
