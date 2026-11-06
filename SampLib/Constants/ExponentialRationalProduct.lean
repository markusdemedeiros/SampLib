import SampLib.Constants.ExpMinusBounds
import SampLib.Bernoulli.Laws.RationalEnclosureScale
import SampLib.Bernoulli.Syntax.Exponential

/-! # Rational multiples of a negative exponential, including compensated scales -/

open ProbLang
open scoped SampLib.ExponentialTerms

namespace SampLib.ExponentialRationalProduct

noncomputable section

def bias (x y z t : ℕ) (h : Real.exp (-((x : ℝ) / y)) * z / t ≤ 1) : unitInterval :=
  ⟨Real.exp (-((x : ℝ) / y)) * z / t, ⟨by positivity, h⟩⟩

private def enclosures (x y z t : ℕ) (hy : 0 < y) (ht : 0 < t)
    (h : Real.exp (-((x : ℝ) / y)) * z / t ≤ 1) (n : ℕ) :
    FromBounds.Interval (bias x y z t h) :=
  ((ExponentialEnclosure.interval x y hy n).scale z t ht).toProbability (bias x y z t h) rfl

@[pl_fold] private def boundsCode {rT : Type} (x y z t : ℕ) : Exp rT := pl%
  fun n,
    let interval := &Occil.Constants.expMinusBounds #int (x : ℤ) #int (y : ℤ) n;
    let low := fst(interval);
    let high := fst(snd(interval));
    let d := snd(snd(interval));
    (#int (z : ℤ) * low, (#int (z : ℤ) * high, #int (t : ℤ) * d))

private def bounds {rT : Type} (x y z t : ℕ) : Val rT :=
  ⟨boundsCode x y z t, by unfold boundsCode; exact .lam (by is_lc), by is_lc⟩

private theorem guard (y t : ℕ) (hy : 0 < y) (ht : 0 < t) :
    (((false || decide ((y : ℤ) ≤ 0)) || false) || decide ((t : ℤ) ≤ 0)) = false := by
  simp [hy.ne', ht.ne']

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_bounds (E : CoPset) (x y z t : ℕ) (hy : 0 < y) (ht : 0 < t)
    (h : Real.exp (-((x : ℝ) / y)) * z / t ≤ 1) (n : ℕ) :
    ⊢ tglWp E pl(&(bounds x y z t : Val rT).fst #int (n : ℤ))
      (fun w : Val rT =>
        iprop(⌜w = FromBounds.encodeInterval (enclosures x y z t hy ht h n)⌝)) := by
  twp_pure
  twp_bind pl(&Occil.Constants.expMinusBounds #int (x : ℤ) #int (y : ℤ) #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply ExponentialEnclosure.twp_expMinusBounds E x y hy n
  iintro %w %hw
  subst w
  twp_pures
  twp_value
  imodintro
  ipureintro
  apply Val.ext
  simp [enclosures, FromBounds.encodeInterval, RealEnclosure.Interval.toProbability,
    RealEnclosure.Interval.scale, RealEnclosure.Interval.triple, Exp.ofVal]

/-- The sole scale restriction is the exact final probability, allowing `z > t`. -/
theorem exponentialRationalProduct_distSpec (E : CoPset) (x y z t : ℕ)
    (hy : 0 < y) (ht : 0 < t) (h : Real.exp (-((x : ℝ) / y)) * z / t ≤ 1) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.exponentialRationalProduct
      #int (x : ℤ) #int (y : ℤ) #int (z : ℤ) #int (t : ℤ) #())
      (RealCoin.law (bias x y z t h)) Val.bool where
  spec F hF := by
    have hsample := (FromBounds.fromBounds_distSpec (rT := rT) (GF := GF) E (bias x y z t h)
      (enclosures x y z t hy ht h)
      ((ExponentialEnclosure.tight x y hy).scale z t ht |>.toProbability (bias x y z t h) rfl)
      (bounds x y z t) (twp_bounds E x y z t hy ht h)).spec F hF
    simp only [bounds, boundsCode, Exp.close, ClosedExp.closeRec, Exp.closeRec,
      Var.internal.injEq, Nat.reduceEqDiff, ↓reduceIte] at hsample
    iintro Hcredit
    iterate 5 twp_pure
    twp_pures
    rw [guard y t hy ht]
    twp_pure
    iapply hsample $$ Hcredit

end specification

end

end SampLib.ExponentialRationalProduct
