import SampLib.Discrete.Laws.BinomialHalfKernel

/-! # Credits for half-binomial rejection

The block, rank, and sign credits unfold the proposal expectation in the
source's sampling order. The acceptance coin then recovers the kernel credit.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.BinomialHalfRejection

noncomputable section

open BinomialHalfEnvelope
open BinomialHalfProposal (candidate acceptance kernel factor)

abbrev law (n : ℕ) := Binomial.law VonNeumann.fairBias n

def signCredit (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (block : ℕ) (rank : Fin (width n)) (sign : Bool) : ℝ≥0∞ :=
  kernel n F ε (block, rank, sign)

def rankCredit (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (block : ℕ) (rank : Fin (width n)) : ℝ≥0∞ :=
  ∫⁻ sign, signCredit n F ε block rank sign ∂VonNeumann.law

def blockCredit (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (block : ℕ) : ℝ≥0∞ :=
  ∫⁻ rank, rankCredit n F ε block rank ∂UniformFin.law (width n)

theorem proposal_expectation (n : ℕ) (hn : Even n) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) :
    ∫⁻ block, blockCredit n F ε block ∂Geometric.law VonNeumann.fairBias =
      (∫⁻ k, F k ∂law n) + ε := by
  have : NeZero (width n) := ⟨Nat.ne_of_gt (width_pos n)⟩
  simp only [blockCredit, rankCredit, signCredit]
  rw [← BinomialHalfProposal.expectation n hn F ε]
  unfold BinomialHalfProposal.law
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro block
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]

def bias (n : ℕ) (hn : Even n) (t : ℕ × (Fin (width n) × Bool)) :
    unitInterval := ⟨acceptance n t, BinomialHalfProposal.acceptance_mem n hn t⟩

def coinCredit (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (t : ℕ × (Fin (width n) × Bool)) (b : Bool) : ℝ≥0∞ :=
  if b then F (candidate n t).toNat else (∫⁻ k, F k ∂law n) + factor * ε

theorem coin_expectation (n : ℕ) (hn : Even n) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (t : ℕ × (Fin (width n) × Bool)) :
    ∫⁻ b, coinCredit n F ε t b ∂RealCoin.law (bias n hn t) = kernel n F ε t := by
  rw [RealCoin.lintegral_law]
  rfl

theorem rejected_credit (n : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (t : ℕ × (Fin (width n) × Bool))
    (h : ¬(0 ≤ candidate n t ∧ candidate n t ≤ n)) :
    kernel n F ε t = (∫⁻ k, F k ∂law n) + factor * ε := by
  simp [kernel, acceptance, h]

end

end SampLib.BinomialHalfRejection
