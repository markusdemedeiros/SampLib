module

public import Metrology.Iris.ErrorCredits
public import Metrology.Iris.LocalBI

@[expose] public section

/-! # Error amplification with a state potential

Every recursive call pays its own potential-weighted credit. A uniform lower
bound on the potential makes a sufficiently amplified credit contradictory,
regardless of the state reached by the call.
-/

open Iris Iris.BI Iris.ProofMode
open scoped ENNReal NNReal

namespace ErrorCredit.Induction

noncomputable section

variable {GF : BundledGFunctors} [ECGS GF] {α : Type _}
local bi (IProp GF)

private theorem weighted_finite (t : α → ℝ≥0) (ht : ∀ x, 1 ≤ t x)
    (P : α → IProp GF) (k : ℝ≥0) (hk : 1 < k) (n : ℕ)
    (ε : ℝ≥0∞) (hε : 0 < ε) (hlarge : 1 ≤ (k : ℝ≥0∞) ^ n * ε) :
    □ (∀ ε : ℝ≥0∞, ⌜0 < ε⌝ -∗
      □ (∀ x, ↯ ((k : ℝ≥0∞) * ε * t x) -∗ P x) -∗
        ∀ x, ↯ (ε * t x) -∗ P x) ⊢
      ∀ x, ↯ (ε * t x) -∗ P x := by
  induction n generalizing ε with
  | zero =>
    have he : 1 ≤ ε := by simpa using hlarge
    iintro #Hstep %x Hcredit
    have hx : (1 : ℝ≥0∞) ≤ t x := by exact_mod_cast ht x
    have hbig : 1 ≤ ε * t x := by simpa using mul_le_mul' he hx
    iexfalso
    iapply ErrorCredit.contradict hbig $$ Hcredit
  | succ n IH =>
    have hpos : 0 < (k : ℝ≥0∞) * ε :=
      ENNReal.mul_pos_iff.mpr ⟨ENNReal.coe_pos.mpr (lt_trans zero_lt_one hk), hε⟩
    have hnext : 1 ≤ (k : ℝ≥0∞) ^ n * ((k : ℝ≥0∞) * ε) := by
      simpa only [pow_succ, mul_assoc] using hlarge
    iintro #Hstep
    iapply Hstep $$ %ε %hε []
    iintro !>
    iapply (IH ((k : ℝ≥0∞) * ε) hpos hnext) $$ Hstep

/-- Persistent recursive hypotheses may be called at several states, provided
each call receives its amplified, potential-weighted credit. -/
theorem weighted (t : α → ℝ≥0) (ht : ∀ x, 1 ≤ t x)
    (P : α → IProp GF) (ε : ℝ≥0∞) (hε : 0 < ε) (k : ℝ≥0) (hk : 1 < k) :
    □ (∀ ε : ℝ≥0∞, ⌜0 < ε⌝ -∗
      □ (∀ x, ↯ ((k : ℝ≥0∞) * ε * t x) -∗ P x) -∗
        ∀ x, ↯ (ε * t x) -∗ P x) ⊢
      ∀ x, ↯ (ε * t x) -∗ P x := by
  obtain ⟨n, hn⟩ := ENNReal.exists_pow_mul_ge_one hε hk
  exact weighted_finite t ht P k hk n ε hε (by simpa only [mul_comm] using hn)

end

end ErrorCredit.Induction
