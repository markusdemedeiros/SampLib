import SampLib.Samplers.GeneralizedContinuedFraction

/-! # Positive simple continued fractions

The source wrapper supplies numerator one to the generalized integer engine.
Its law is the same canonical finite-prefix fraction, with simple coefficients.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.SimpleContinuedFraction

noncomputable section

/-- A positive simple coefficient, optionally the last coefficient. -/
structure Coefficient where
  denominator : ℕ
  positive : 0 < denominator
  last : Bool

def Coefficient.generalized (c : Coefficient) : ContinuedFraction.Coefficient :=
  ⟨1, c.denominator, by decide, c.positive, c.last⟩

def sequence (a : ℕ → Coefficient) (i : ℕ) : ContinuedFraction.Coefficient :=
  (a i).generalized

/-- The value of the simple fraction beginning at the source's first position. -/
abbrev bias (a : ℕ → Coefficient) := ContinuedFraction.value (sequence a) 1

/-- The source callback returns `(a,last)`. -/
def encodeCoefficient {rT : Type _} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.denominator) (Val.bool c.last)

private def liftOracle {rT : Type _} (coefficient : Val rT) : Val rT :=
  ⟨.lam (.pair (.lit (.int 1)) (.app coefficient.fst (.bvar 0))),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_liftOracle (E : CoPset) (a : ℕ → Coefficient) (coefficient : Val rT)
    (horacle : ∀ i, ContinuedFraction.Reachable (sequence a) 1 i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (i : ℕ) (hi : ContinuedFraction.Reachable (sequence a) 1 i) :
    ⊢ tglWp E pl(&(liftOracle coefficient).fst #int (i : ℤ))
      (fun v : Val rT => iprop(⌜v = ContinuedFraction.encodeCoefficient (sequence a i)⌝)) := by
  twp_pure
  twp_bind pl(&coefficient.fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply horacle i hi
  iintro %v %hv
  subst v
  twp_value
  imodintro
  ipureintro
  rfl

/-- Execute the source adapter, then the generalized continued-fraction specification. -/
theorem twp_continuedFraction (E : CoPset) (a : ℕ → Coefficient) (coefficient : Val rT)
    (horacle : ∀ i, ContinuedFraction.Reachable (sequence a) 1 i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a) F) -∗
      tglWp E pl(&Occil.Constants.continuedFraction &coefficient.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have h := ContinuedFraction.twp_generalizedContinuedFraction (rT := rT) (GF := GF)
    E (sequence a) 1 (liftOracle coefficient) (twp_liftOracle E a coefficient horacle) F
  iintro Hcredit
  iterate 2 twp_pure
  simp only [ContinuedFraction.generalizedContinuedFraction_closeRec,
    ContinuedFraction.generalizedContinuedFraction_openRec]
  ieval (
    change _ ⊢ tglWp E
      pl(&Occil.Constants.generalizedContinuedFraction &(liftOracle coefficient).fst #1) _)
  iapply h $$ Hcredit

/-- Bernoulli at the canonical positive simple continued fraction. -/
theorem continuedFraction_distSpec (E : CoPset) (a : ℕ → Coefficient) (coefficient : Val rT)
    (horacle : ∀ i, ContinuedFraction.Reachable (sequence a) 1 i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.continuedFraction &coefficient.fst #())
      (RealCoin.law (bias a)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_continuedFraction E a coefficient horacle F)

end specification

end

end SampLib.SimpleContinuedFraction
