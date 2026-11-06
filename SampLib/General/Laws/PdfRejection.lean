import SampLib.Common.Laws.AcceptedProposal
import SampLib.General.Laws.IntegerThreshold
import SampLib.Uniform.Laws.RndIntExcRange

/-! # Integer density rejection law -/

open MeasureTheory
open scoped ENNReal

namespace SampLib.PdfRejection

noncomputable section

/-- A nonnegative integer height function bounded by a positive envelope. -/
structure Model where
  lower : ℤ
  upper : ℤ
  interval : lower < upper
  envelope : ℕ
  positive : 0 < envelope
  height : ℤ → ℕ
  bounded : ∀ x ∈ Set.Ico lower upper, height x ≤ envelope

abbrev proposal (D : Model) := RndIntExcRange.law D.lower D.upper D.interval

/-- Outside the proposal interval, the arbitrary acceptance extension is zero. -/
def acceptance (D : Model) (x : ℤ) : unitInterval :=
  if hx : x ∈ Set.Ico D.lower D.upper then
    IntegerThreshold.bias (D.height x) D.envelope D.positive (D.bounded x hx)
  else 0

/-- Uniform proposal mass weighted by its integer-height acceptance probability. -/
abbrev law (D : Model) (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0) :=
  AcceptedProposal.law (proposal D) (acceptance D) hmass

/-- Credits returned by the acceptance comparison. -/
def coinCredit (D : Model) (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (x : ℤ) (b : Bool) : ℝ≥0∞ :=
  if b then F x else AcceptedProposal.credit (proposal D) (acceptance D) hmass F +
    AcceptedProposal.factor (proposal D) (acceptance D) * ε

theorem coin_expectation (D : Model)
    (hmass : AcceptedProposal.mass (proposal D) (acceptance D) ≠ 0)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (x : ℤ) (hx : x ∈ Set.Ico D.lower D.upper) :
    RealCoin.credit
      (IntegerThreshold.bias (D.height x) D.envelope D.positive (D.bounded x hx))
      (coinCredit D hmass F ε x) =
      AcceptedProposal.kernel (proposal D) (acceptance D) hmass F ε x := by
  simp [RealCoin.credit, RealCoin.pmf, coinCredit, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, acceptance, hx]

end

end SampLib.PdfRejection
