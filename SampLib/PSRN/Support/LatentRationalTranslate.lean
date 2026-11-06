import SampLib.PSRN.Support.LatentRational
import SampLib.PSRN.Support.LatentRealMap

/-! # Rational translation of a deferred real

Adding a rational constant changes neither the source posterior nor its interval
error. The translated closure retains the original source's physical ownership.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace Model

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Translation retains the full shared latent state. -/
def translate (D : Model Ω S) (c : ℝ) : Model Ω S :=
  { D with
    value := fun x => c + D.value x
    measurable_value := D.measurable_value.const_add c }

theorem translate_law (D : Model Ω S) (c : ℝ) (s : S) :
    (D.translate c).law s = (D.law s).map (fun x => c + x) := by
  have hm : Measurable (fun x : ℝ => c + x) := by fun_prop
  rw [law, law, Measure.map_map hm D.measurable_value]
  rfl

/-- A zero-width rational interval translates the source enclosure exactly. -/
theorem encloses_translate (D : Model Ω S) {s : S} {n : ℕ} {I : RationalInterval}
    (hI : D.Encloses s n I) (a b : ℤ) (hb : 0 < b) :
    (D.translate ((a : ℝ) / b)).Encloses s n ((RationalInterval.point a b hb).add I) := by
  refine hI.mono fun x hx => ⟨?_, ?_⟩
  · exact RationalInterval.contains_add _ _
      ((RationalInterval.contains_point a b hb _).mpr rfl) hx.1
  · change ((RationalInterval.point a b hb).add I).width ≤ D.error n x
    rw [RationalInterval.width_add]
    simpa only [RationalInterval.width, RationalInterval.point, RationalInterval.upperReal,
      RationalInterval.lowerReal, sub_self, zero_add] using hx.2

end Model

private def translateCode {rT : Type} (source : Exp rT) (a b : ℤ) : Exp rT :=
  let result := .pair
    (.binop .plus
      (.binop .mult (.fst (.bvar 3)) (.snd (.bvar 0)))
      (.binop .mult (.fst (.bvar 2)) (.snd (.bvar 1))))
    (.pair
      (.binop .plus
        (.binop .mult (.fst (.bvar 1)) (.snd (.bvar 0)))
        (.binop .mult (.fst (.bvar 0)) (.snd (.bvar 1))))
      (.binop .mult (.snd (.bvar 1)) (.snd (.bvar 0))))
  let ranges := .app (.lam (.app (.lam result) (.snd (.bvar 1)))) (.snd (.bvar 1))
  let right := .app (.lam ranges) (.app source (.bvar 1))
  .lam (.app (.lam right) (.app (LatentRational.value a b).fst (.bvar 0)))

/-- The translated oracle's actual closure, with the source inserted after closing binders. -/
def translateVal {rT : Type} (source : Val rT) (a b : ℤ) : Val rT :=
  ⟨translateCode source.fst a b, .lam (by
    apply Exp.lcb_imp_lc
    have hs (n : ℕ) : Exp.lcb n source.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le n)
    simp [Exp.lcb, LatentRational.value, hs]), by
    apply Exp.lcb_imp_lc
    have hs (n : ℕ) : Exp.lcb n source.fst = true :=
      Exp.lcb_mono (Exp.lc_imp_lcb source.lc) (Nat.zero_le n)
    simp [translateCode, Exp.lcb, LatentRational.value, hs]⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Translation owns exactly the original source oracle. -/
def translateOwns (owns : Val rT → S → IProp GF) (a b : ℤ)
    (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ source : Val rT, ⌜v = translateVal source a b⌝ ∗ owns source s)

/-- Constructing the translation does not observe the source. -/
theorem twp_translate (E : CoPset) (owns : Val rT → S → IProp GF)
    (source : Val rT) (s : S) (a b : ℤ) (hb : 0 < b) :
    iprop(owns source s) ⊢
      tglWp E pl(&Occil.PSRN.add (&Occil.PSRN.rational #a #b) &source.fst)
        (fun v => translateOwns owns a b v s) := by
  iintro Hstate
  twp_pures
  rw [decide_eq_false (not_le.mpr hb)]
  twp_pures
  twp_value
  imodintro
  isimp only [translateOwns]
  iexists source
  iframe Hstate
  ipureintro
  apply Val.ext
  simp [translateVal, translateCode, LatentRational.value]

/-- Observations preserve the entire joint credit and the same physical source. -/
theorem translate_oracleSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D owns)
    (a b : ℤ) (hb : 0 < b) :
    IsOracleSpec E (D.translate ((a : ℝ) / b)) (translateOwns owns a b) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [translateOwns] at Hstate
    icases Hstate with ⟨%source, %hsourceVal, Hstate⟩
    subst v
    twp_pures
    twp_bind pl(&source.fst #int (n : ℤ))
    isimp only [Model.translate] at Hcredit
    iapply hsource.wp source s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    twp_pures
    twp_value
    imodintro
    iexists t, (RationalInterval.point a b hb).add I
    isplit
    · ipureintro
      refine ⟨?_, hI.1, D.encloses_translate hI.2 a b hb⟩
      apply Val.ext
      simp [intervalVal, RationalInterval.add, RationalInterval.point, Exp.ofVal]
    isplitl [Hstate]
    · isimp only [translateOwns]
      iexists source
      iframe Hstate
      itrivial
    isimp only [Model.translate]
    iframe Hcredit

/-- Rational translation composes with a sampler that constructs its source oracle. -/
theorem translate_latentDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S)
    (initial : S) (owns : Val rT → S → IProp GF)
    (hsource : IsLatentDistSpec E e D initial owns) (a b : ℤ) (hb : 0 < b) :
    IsLatentDistSpec E pl(&Occil.PSRN.add (&Occil.PSRN.rational #a #b) &e)
      (D.translate ((a : ℝ) / b)) initial (translateOwns owns a b) where
  oracle := translate_oracleSpec E D owns hsource.oracle a b hb
  spec F hF := by
    iintro Hcredit
    isimp only [Model.translate] at Hcredit
    twp_bind e
    iapply hsource.wp F hF _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    simp only [Exp.ofVal]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_translate E owns source t a b hb $$ Hstate
    iintro %v Hstate
    iexists t
    isimp only [Model.translate]
    iframe Hstate Hcredit
    ipureintro
    exact ht

end specification

end

end SampLib.LatentReal
