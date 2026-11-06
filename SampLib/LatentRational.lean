import SampLib.LatentSpec
import Samplers.PSRN.Core

/-! # Rational constants as degenerate latent real oracles -/

open ProbLang
open MeasureTheory (Measure)
open scoped ENNReal

namespace SampLib.LatentRational

noncomputable section

/-- A constant real has a singleton latent space and zero observation error. -/
def model (a d : ℤ) : LatentReal.Model Unit Unit where
  posterior _ := Measure.dirac ()
  probability _ := inferInstance
  value _ := (a : ℝ) / d
  measurable_value := measurable_const
  refines _ _ := True
  refines_refl _ := trivial
  refines_trans _ _ := trivial
  absolutelyContinuous _ := Measure.AbsolutelyContinuous.refl _
  error _ _ := 0
  error_tendsto _ := Filter.Eventually.of_forall fun _ => tendsto_const_nhds

@[simp] theorem model_law (a d : ℤ) :
    (model a d).law () = Measure.dirac ((a : ℝ) / d) := by
  simp [LatentReal.Model.law, model]

/-- A constant oracle returns the same exact interval at every precision. -/
def value {rT : Type} (a d : ℤ) : Val rT :=
  ⟨.lam (.pair (.lit (.int a)) (.pair (.lit (.int a)) (.lit (.int d)))),
    .lam (by is_lc), by is_lc⟩

theorem interval_encloses (a d : ℤ) (hd : 0 < d) (n : ℕ) :
    (model a d).Encloses () n (LatentReal.RationalInterval.point a d hd) := by
  apply Filter.Eventually.of_forall
  intro x
  refine ⟨?_, ?_⟩
  · exact (LatentReal.RationalInterval.contains_point _ _ _ _).mpr rfl
  · simp [LatentReal.RationalInterval.upperReal, LatentReal.RationalInterval.lowerReal,
      LatentReal.RationalInterval.point, model]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A constant requires no private heap state. -/
def owns (a d : ℤ) (v : Val rT) (_ : Unit) : IProp GF := iprop(⌜v = value a d⌝)

/-- Every observation of the constant preserves the caller's latent credit. -/
theorem oracleSpec (E : CoPset) (a d : ℤ) (hd : 0 < d) :
    LatentReal.IsOracleSpec (GF := GF) E (model a d) (owns a d) where
  observe v s n F _ := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    ihave %hv := Hstate
    subst v
    unfold value
    twp_pures
    twp_value
    imodintro
    iexists (), LatentReal.RationalInterval.point a d hd
    cases s
    iframe Hcredit
    isplitl []
    · ipureintro
      exact ⟨rfl, trivial, interval_encloses a d hd n⟩
    isimp only [owns]
    ipureintro
    rfl

/-- The actual rational constructor supplies an exact constant oracle. -/
theorem rational_latentDistSpec (E : CoPset) (a d : ℤ) (hd : 0 < d) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.rational #int a #int d)
      (model a d) () (owns a d) where
  oracle := oracleSpec E a d hd
  spec F _ := by
    iintro Hcredit
    twp_pures
    have htest : decide (d ≤ 0) = false := by simp [not_le.mpr hd]
    isimp only [htest]
    twp_pures
    twp_value
    imodintro
    iexists ()
    iframe Hcredit
    isplitl []
    · ipureintro
      trivial
    isimp only [owns]
    ipureintro
    rfl

end specification

end

end SampLib.LatentRational
