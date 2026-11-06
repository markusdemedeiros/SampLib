import SampLib.Constants.Laws.CriticalCoin
import SampLib.Uniform.RealCoin
import SampLib.Bernoulli.VonNeumann

/-! # Continuation credits for critical two-call recursion

Finite trees pay the returned-outcome expectation and one unit on each unresolved
branch. All coefficient identities live in nonnegative reals, so their transport
preserves arbitrary, possibly infinite, continuation credits.
-/

open scoped ENNReal NNReal

namespace SampLib.CriticalCoin

noncomputable section

private def trueWeight (a : ℕ → Coefficient) (n i : ℕ) : ℝ≥0 :=
  NNReal.mk (masses a n i).1 (masses_valid a n i).1

private def falseWeight (a : ℕ → Coefficient) (n i : ℕ) : ℝ≥0 :=
  NNReal.mk (masses a n i).2 (masses_valid a n i).2.1

private def missingWeight (a : ℕ → Coefficient) (n i : ℕ) : ℝ≥0 :=
  NNReal.mk (1 - (masses a n i).1 - (masses a n i).2)
    (by linarith [(masses_valid a n i).2.2])

private def inputWeight (a : ℕ → Coefficient) (i : ℕ) : ℝ≥0 :=
  NNReal.mk (a i).bias (a i).bias.2.1

private def complementWeight (a : ℕ → Coefficient) (i : ℕ) : ℝ≥0 :=
  NNReal.mk (1 - ((a i).bias : ℝ)) (sub_nonneg.mpr (a i).bias.2.2)

private theorem trueWeight_succ (a : ℕ → Coefficient) (n i : ℕ)
    (hlast : (a i).last = false) :
    trueWeight a (n + 1) i =
      (inputWeight a i + falseWeight a n (i + 1) * trueWeight a n i) / 2 := by
  apply NNReal.eq
  simp only [trueWeight, falseWeight, inputWeight, masses, hlast,
    Bool.false_eq_true, ite_false, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_mk]

private theorem falseWeight_succ (a : ℕ → Coefficient) (n i : ℕ)
    (hlast : (a i).last = false) :
    falseWeight a (n + 1) i =
      (complementWeight a i + trueWeight a n (i + 1) +
        falseWeight a n (i + 1) * falseWeight a n i) / 2 := by
  apply NNReal.eq
  simp only [trueWeight, falseWeight, complementWeight, masses, hlast,
    Bool.false_eq_true, ite_false, NNReal.coe_div, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat, NNReal.coe_mk]

private theorem missingWeight_succ (a : ℕ → Coefficient) (n i : ℕ)
    (hlast : (a i).last = false) :
    missingWeight a (n + 1) i =
      (missingWeight a n (i + 1) + falseWeight a n (i + 1) * missingWeight a n i) / 2 := by
  apply NNReal.eq
  simp only [missingWeight, falseWeight, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_mk]
  exact deficit_succ a n i hlast

/-- Finite return expectation, plus the exact unresolved mass. -/
def credit (a : ℕ → Coefficient) (n i : ℕ) (F : Bool → ℝ≥0∞) : ℝ≥0∞ :=
  (trueWeight a n i : ℝ≥0∞) * F true +
    (falseWeight a n i : ℝ≥0∞) * F false + missingWeight a n i

@[simp] theorem credit_zero (a : ℕ → Coefficient) (i : ℕ) (F : Bool → ℝ≥0∞) :
    credit a 0 i F = 1 := by
  simp [credit, trueWeight, falseWeight, missingWeight, masses]

/-- The tail's success stops with false; its failure pays the finite retry. -/
def tailCredit (a : ℕ → Coefficient) (n i : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then F false else credit a n i F

def branchCredit (a : ℕ → Coefficient) (n i : ℕ) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then RealCoin.credit (a i).bias F
  else credit a n (i + 1) (tailCredit a n i F)

private theorem input_credit (a : ℕ → Coefficient) (i : ℕ) (F : Bool → ℝ≥0∞) :
    RealCoin.credit (a i).bias F =
      (complementWeight a i : ℝ≥0∞) * F false + (inputWeight a i : ℝ≥0∞) * F true := by
  simp only [RealCoin.credit, RealCoin.pmf]
  rw [ENNReal.ofReal_eq_coe_nnreal (sub_nonneg.mpr (a i).bias.2.2),
    ENNReal.ofReal_eq_coe_nnreal (a i).bias.2.1]
  simpa only [inputWeight, complementWeight, Bool.false_eq_true, ite_true, ite_false] using
    add_comm ((inputWeight a i : ℝ≥0∞) * F true)
      ((complementWeight a i : ℝ≥0∞) * F false)

/-- A final coefficient returns immediately, without unresolved recursion. -/
theorem credit_last (a : ℕ → Coefficient) (n i : ℕ) (hlast : (a i).last = true)
    (F : Bool → ℝ≥0∞) : credit a (n + 1) i F = RealCoin.credit (a i).bias F := by
  rw [input_credit]
  simp only [credit, trueWeight, falseWeight, missingWeight, masses, hlast, ite_true,
    sub_self, NNReal.mk_zero, ENNReal.coe_zero, add_zero]
  exact add_comm _ _

/-- One fair decision and both possible recursive calls preserve the finite-tree budget. -/
theorem expectation (a : ℕ → Coefficient) (n i : ℕ)
    (hlast : (a i).last = false) (F : Bool → ℝ≥0∞) :
    RealCoin.credit VonNeumann.fairBias (branchCredit a n i F) = credit a (n + 1) i F := by
  rw [RealCoin.credit]
  simp only [RealCoin.pmf, VonNeumann.fairBias,
    branchCredit, Bool.false_eq_true, ite_false, ite_true]
  rw [input_credit]
  simp only [credit, tailCredit, Bool.false_eq_true, ite_false, ite_true,
    trueWeight_succ a n i hlast, falseWeight_succ a n i hlast,
    missingWeight_succ a n i hlast,
    ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
    ENNReal.coe_ofNat]
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  simp only [ENNReal.div_eq_inv_mul]
  ring

/-- The finite-tree budget converges for every continuation, including infinite credits. -/
theorem credit_tendsto (a : ℕ → Coefficient) (i : ℕ) (F : Bool → ℝ≥0∞) :
    Filter.Tendsto (fun n => credit a n i F) Filter.atTop
      (nhds (RealCoin.credit (bias a i) F)) := by
  have ht := ENNReal.Tendsto.mul_const (b := F true)
    (ENNReal.tendsto_ofReal (true_tendsto a i))
    (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (bias_pos a i))))
  have hf : Filter.Tendsto
      (fun n => ENNReal.ofReal (masses a n i).2 * F false) Filter.atTop
      (nhds (ENNReal.ofReal (1 - (bias a i : ℝ)) * F false)) := by
    by_cases hb : (bias a i : ℝ) = 1
    · have hz (n : ℕ) : (masses a n i).2 = 0 := by
        have h := (masses_le a n i).2
        rw [hb] at h
        exact le_antisymm (by linarith) (masses_valid a n i).2.1
      simpa only [hz, hb, sub_self, ENNReal.ofReal_zero, zero_mul] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ≥0∞))
          Filter.atTop (nhds 0))
    · have hp : 0 < 1 - (bias a i : ℝ) := by
        have h := (bias a i).2.2
        exact sub_pos.mpr (lt_of_le_of_ne h hb)
      exact ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (false_tendsto a i))
        (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
  have hm := ENNReal.tendsto_ofReal (missing_tendsto a i)
  have h := (ht.add hf).add hm
  have htcoe (n : ℕ) : (trueWeight a n i : ℝ≥0∞) =
      ENNReal.ofReal (masses a n i).1 :=
    (ENNReal.ofReal_eq_coe_nnreal (masses_valid a n i).1).symm
  have hfcoe (n : ℕ) : (falseWeight a n i : ℝ≥0∞) =
      ENNReal.ofReal (masses a n i).2 :=
    (ENNReal.ofReal_eq_coe_nnreal (masses_valid a n i).2.1).symm
  have hmcoe (n : ℕ) : (missingWeight a n i : ℝ≥0∞) =
      ENNReal.ofReal (1 - (masses a n i).1 - (masses a n i).2) :=
    (ENNReal.ofReal_eq_coe_nnreal (by linarith [(masses_valid a n i).2.2])).symm
  simpa only [credit, htcoe, hfcoe, hmcoe, RealCoin.credit, RealCoin.pmf,
    ENNReal.ofReal_zero, add_zero, zero_add, Bool.false_eq_true, ite_true, ite_false,
    add_comm] using h

end

end SampLib.CriticalCoin
