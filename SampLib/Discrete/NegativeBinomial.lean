import SampLib.Discrete.Geometric
import Metrology.Iris.LocalBI

/-!
# Negative-binomial failure counts

The target law is the sum of independent geometric failure counts, one for each
required success. Finite induction follows ProbLang's right-to-left evaluation
order and composes the geometric specification.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.NegativeBinomial

noncomputable section

section distribution

open MeasureTheory Measure

/-- Sum of `r` independent geometric failure counts; zero successes return zero. -/
def law (p : unitInterval) : ℕ → Measure ℕ
  | 0 => dirac 0
  | r + 1 => ((law p r).prod (Geometric.law p)).map (fun z => z.2 + z.1)

instance (p : unitInterval) (r : ℕ) : IsProbabilityMeasure (law p r) := by
  induction r with
  | zero => dsimp [law]; infer_instance
  | succ r ih =>
    let := ih
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Expected continuation credit. -/
def credit (p : unitInterval) (r : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ n, F n ∂law p r

/-- The remaining credit after observing the first geometric count. -/
def firstCredit (p : unitInterval) (F : ℕ → ℝ≥0∞) (y : ℕ) : ℝ≥0∞ :=
  Geometric.credit p (fun x => F (x + y))

/-- Independence turns the convolution expectation into two successive expectations. -/
theorem credit_succ (p : unitInterval) (r : ℕ) (F : ℕ → ℝ≥0∞) :
    credit p (r + 1) F = credit p r (firstCredit p F) := by
  rw [credit, law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

end distribution

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS
open MeasureTheory (lintegral_dirac)

private theorem geometric_close {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.geometric : Exp rT) = Occil.geometric :=
  Exp.closeRec_fresh x _ k (by simp [Occil.geometric, Exp.fv])

private theorem geometric_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (Occil.geometric : Exp rT) = Occil.geometric :=
  (Exp.open_lc k e _ (by is_lc)).symm

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Negative-binomial failure counts, including zero requested successes. -/
theorem twp_negativeBinomial (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (r : ℕ) (hp : r = 0 ∨ 0 < (p : ℝ)) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit p r F) -∗
      tglWp E pl(&Occil.negativeBinomial &coin.fst #int (r : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  induction r generalizing F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [credit, law, lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ r IH =>
    have hp' : 0 < (p : ℝ) := hp.resolve_left (Nat.succ_ne_zero r)
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    simp only [geometric_close, geometric_open]
    twp_bind pl(&Occil.negativeBinomial &coin.fst #int (r : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply IH (Or.inr hp') (firstCredit p F)
      isimp only [credit_succ] at Hcredit
      iexact Hcredit
    iintro %v ⟨%y, %hv, Hcredit⟩
    subst v
    twp_bind pl(&Occil.geometric &coin.fst #())
    isimp only [firstCredit, Geometric.credit] at Hcredit
    iapply ((Geometric.geometric_distSpec E p hp' coin hcoin).wp
      (fun x => F (x + y)) (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    twp_pures
    rw [← Nat.cast_add]
    twp_value
    imodintro
    iexists x + y
    iframe Hcredit
    itrivial

/-- Typed negative-binomial specification. -/
theorem negativeBinomial_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (r : ℕ) (hp : r = 0 ∨ 0 < (p : ℝ)) :
    IsDistSpec (GF := GF) E pl(&Occil.negativeBinomial &coin.fst #int (r : ℤ))
      (law p r) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    simpa only [credit] using wand_entails (twp_negativeBinomial E p coin hcoin r hp F)

end specification

end

end SampLib.NegativeBinomial
