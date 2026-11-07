import SampLib.General.Laws.LinearBin
import SampLib.Core.Retry
import SampLib.General.Support.IntegerThreshold
import SampLib.Core.SupportedSpec

/-! # Rejection inside one linearly interpolated integer bin -/

open ProbLang
open scoped ENNReal

namespace SampLib.LinearBin

noncomputable section

@[pl_fold] def draw {rT : Type _} (D : Model) : Exp rT := pl%
  rec retry u :=
    let offset := &Occil.uniformInt #int (D.width : ℤ);
    let height := #int (D.ha : ℤ) * (#int (D.width : ℤ) - offset) +
      #int (D.hb : ℤ) * offset;
    if &Occil.uniformInt (#int (D.width : ℤ) * #int (envelope D : ℤ)) < height then
      #int D.left + offset else retry #()

section mathematics

open MeasureTheory

def coinCredit (D : Model) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) (b : Bool) : ℝ≥0∞ :=
  if b then F (D.left + (k : ℤ)) else
    AcceptedProposal.credit (UniformInt.law D.width) (acceptance D) (mass_ne_zero D)
      (fun j => F (D.left + (j : ℤ))) +
      AcceptedProposal.factor (UniformInt.law D.width) (acceptance D) * ε

private theorem coin_expectation (D : Model) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞)
    (k : ℕ) (hk : k < D.width) :
    RealCoin.credit (IntegerThreshold.bias (height D k) (D.width * envelope D)
      (denominator_pos D) (height_le D k hk)) (coinCredit D F ε k) =
      AcceptedProposal.kernel (UniformInt.law D.width) (acceptance D) (mass_ne_zero D)
        (fun j => F (D.left + (j : ℤ))) ε k := by
  simp [RealCoin.credit, RealCoin.pmf, coinCredit, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, acceptance, hk]

private theorem credit_eq (D : Model) (F : ℤ → ℝ≥0∞) :
    ∫⁻ x, F x ∂law D =
      AcceptedProposal.credit (UniformInt.law D.width) (acceptance D) (mass_ne_zero D)
        (fun k => F (D.left + (k : ℤ))) := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

end mathematics

private theorem height_cast (D : Model) (k : ℕ) (hk : k < D.width) :
    (D.ha : ℤ) * ((D.width : ℤ) - (k : ℤ)) + (D.hb : ℤ) * (k : ℤ) =
      (height D k : ℤ) := by
  simp only [height, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk.le]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_draw (E : CoPset) (D : Model) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ x, F x ∂law D) -∗ tglWp E pl(&(draw D) #())
      (fun v : Val rT => iprop(∃ x : ℤ, ⌜v = Val.int x⌝ ∗ ↯ (F x))) := by
  iintro Hcredit
  isimp only [credit_eq] at Hcredit
  irevert Hcredit
  iapply Retry.twp_loop solve_not_value
    (AcceptedProposal.one_lt_factor (UniformInt.law D.width) (acceptance D) (mass_ne_zero D))
  iintro !> %ε %hε IH Hcredit
  iterate 2 twp_pure
  simp only [UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec]
  twp_bind pl(&Occil.uniformInt #int (D.width : ℤ))
  ihave Hsample := ErrorCredit.weaken
    (AcceptedProposal.expectation_preservation (UniformInt.law D.width) (acceptance D)
      (measurable_of_countable _) (mass_ne_zero D) (fun j => F (D.left + (j : ℤ)))
      (measurable_of_countable _) ε) $$ Hcredit
  iapply ((UniformInt.uniformInt_distSpec E D.width).wp_supported
    (fun k => k < D.width) (Set.to_countable _).measurableSet (UniformInt.ae_lt D.width)
    (AcceptedProposal.kernel (UniformInt.law D.width) (acceptance D) (mass_ne_zero D)
      (fun j => F (D.left + (j : ℤ))) ε) (measurable_of_countable _) _) $$ Hsample
  iintro %k %hk Hcredit
  iterate 6 twp_pure
  rw [height_cast D k hk]
  simp only [UniformInt.uniformInt_openRec]
  twp_pure
  rw [← Nat.cast_mul]
  twp_bind pl(&Occil.uniformInt #int ((D.width * envelope D : ℕ) : ℤ)
    < #int (height D k : ℤ))
  isimp only [← coin_expectation D F ε k hk, ← RealCoin.lintegral_law] at Hcredit
  iapply ((IntegerThreshold.threshold_distSpec E (height D k) (D.width * envelope D)
    (denominator_pos D) (height_le D k hk)).wp (coinCredit D F ε k)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  cases b
  · twp_pure
    isimp only [coinCredit, Bool.false_eq_true, ite_false] at Hcredit
    isimp [draw, Exp.close, Exp.closeRec] at IH
    iapply IH $$ Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists D.left + (k : ℤ)
    isimp only [coinCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

end specification

end

end SampLib.LinearBin
