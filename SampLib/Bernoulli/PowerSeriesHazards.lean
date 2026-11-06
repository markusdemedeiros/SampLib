import SampLib.Bernoulli.Laws.PowerSeriesHazards
import Samplers.Bernoulli.Series
import SampLib.Uniform.RationalCoin

/-! # Infinite nonnegative power-series factories

The two coin calls give marked exits. A finite uncertainty horizon accounts for
termination even when hazards vanish and the expected running time is infinite.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PowerSeriesHazards

noncomputable section

/-- One exact rational hazard probability, including zero and one. -/
structure Coefficient where
  numerator : ℕ
  denominator : ℕ
  positive : 0 < denominator
  bounded : numerator ≤ denominator

def Coefficient.bias (c : Coefficient) : unitInterval :=
  RationalCoin.bias c.numerator c.denominator (by omega) (by exact_mod_cast c.positive)
    (by exact_mod_cast c.bounded)

def Coefficient.encode {rT : Type _} (c : Coefficient) : Val rT :=
  .pair (.int c.numerator) (.int c.denominator)

def outputLaw (p : unitInterval) (a : ℕ → Coefficient)
    (_absorbs : Filter.Tendsto
      (AbsorbingChain.survival (fun n => continuation p (a n).bias) 0)
      Filter.atTop (nhds 0)) : MeasureTheory.Measure Bool := law p (fun n => (a n).bias) 0

instance (p : unitInterval) (a : ℕ → Coefficient)
    (absorbs : Filter.Tendsto
      (AbsorbingChain.survival (fun n => continuation p (a n).bias) 0)
      Filter.atTop (nhds 0)) : MeasureTheory.IsProbabilityMeasure (outputLaw p a absorbs) :=
  isProbabilityMeasure_law p (fun n => (a n).bias) 0 absorbs

/-- Close the source binders before inserting the arbitrary callback values. -/
private def loop {rT : Type _} (coin hazard : Val rT) : Exp rT :=
  let again := pl({Exp.bvar 2} ({Exp.bvar 1} + #1))
  let stop := .cond
    pl(&Occil.rationalCoin (fst({Exp.bvar 0})) (snd({Exp.bvar 0}))) pl(#false) again
  .fix (.lam (.cond pl(&coin.fst #()) pl(#true)
    (.app (.lam stop) pl(&hazard.fst {Exp.bvar 0}))))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem coefficient_spec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (c.numerator : ℤ) #int (c.denominator : ℤ))
      (RealCoin.law c.bias) Val.bool :=
  RationalCoin.rationalCoin_distSpec E c.numerator c.denominator
    (by omega) (by exact_mod_cast c.positive) (by exact_mod_cast c.bounded)

private def post (F : Bool → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))

private theorem twp_step (E : CoPset) (p : unitInterval) (a : ℕ → Coefficient)
    (coin hazard : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hhazard : ∀ n : ℕ, ⊢ tglWp E pl(&hazard.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (a n).encode⌝)))
    (F : Bool → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞)
    (next : ⊢ ↯ c -∗ tglWp E pl(&(loop coin hazard) #int ((n + 1 : ℕ) : ℤ)) (post F)) :
    ⊢ ↯ (exit p (a n).bias F + continuation p (a n).bias * c) -∗
      tglWp E pl(&(loop coin hazard) #int (n : ℤ)) (post F) := by
  simp only [loop] at next
  iintro Hcredit
  twp_pures
  twp_bind pl(&coin.fst #())
  isimp only [← step_expectation p (a n).bias F c] at Hcredit
  iapply (hcoin.wp (kernel (a n).bias F c) (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pures
    twp_bind pl(&hazard.fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hhazard n
    iintro %v %hv
    subst v
    iterate 3 twp_pure
    simp only [RationalCoin.rationalCoin_openRec]
    twp_bind pl(&Occil.rationalCoin #int ((a n).numerator : ℤ)
      #int ((a n).denominator : ℤ))
    isimp only [kernel, Bool.false_eq_true, ite_false, ← RealCoin.lintegral_law] at Hcredit
    iapply ((coefficient_spec E (a n)).wp
      (fun b => if b then F false else c) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · iterate 2 twp_pure
      rw [← Nat.cast_add_one]
      isimp only [Bool.false_eq_true, ite_false] at Hcredit
      iapply next $$ Hcredit
    · twp_pures
      twp_value
      isimp only [post]
      imodintro
      iexists false
      isimp only [ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_value
    isimp only [post]
    imodintro
    iexists true
    isimp only [kernel, ite_true] at Hcredit
    iframe Hcredit
    itrivial

private theorem twp_loop (E : CoPset) (p : unitInterval) (a : ℕ → Coefficient)
    (coin hazard : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hhazard : ∀ n : ℕ, ⊢ tglWp E pl(&hazard.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (a n).encode⌝)))
    (F : Bool → ℝ≥0∞)
    (absorbs : Filter.Tendsto
      (AbsorbingChain.survival (fun n => continuation p (a n).bias) 0)
      Filter.atTop (nhds 0)) :
    ⊢ ↯ (∫⁻ b, F b ∂law p (fun n => (a n).bias) 0) -∗
      tglWp E pl(&(loop coin hazard) #0) (post F) := by
  apply AbsorbingChain.twp_of_survival E
    (fun n => pl(&(loop coin hazard) #int (n : ℤ))) _
    (fun n => continuation p (a n).bias) (fun n => exit p (a n).bias F)
    (fun n => ∫⁻ b, F b ∂law p (fun n => (a n).bias) n)
    (fun n => expectation p (fun n => (a n).bias) n F)
    (twp_step E p a coin hazard hcoin hhazard F) 0 rfl absorbs

/-- All rational hazard sequences whose continuation products vanish, without moment bounds. -/
theorem powerSeriesHazards_distSpec (E : CoPset) (p : unitInterval) (a : ℕ → Coefficient)
    (coin hazard : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hhazard : ∀ n : ℕ, ⊢ tglWp E pl(&hazard.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (a n).encode⌝)))
    (absorbs : Filter.Tendsto
      (AbsorbingChain.survival (fun n => continuation p (a n).bias) 0)
      Filter.atTop (nhds 0)) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.powerSeriesHazards
      &coin.fst &hazard.fst #()) (outputLaw p a absorbs) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [outputLaw] at Hcredit
    iterate 4 twp_pure
    simp only [RationalCoin.rationalCoin_closeRec, RationalCoin.rationalCoin_openRec]
    have h := twp_loop E p a coin hazard hcoin hhazard F absorbs
    simp only [loop] at h
    unfold post at h
    iapply h $$ Hcredit

end specification

end

end SampLib.PowerSeriesHazards
