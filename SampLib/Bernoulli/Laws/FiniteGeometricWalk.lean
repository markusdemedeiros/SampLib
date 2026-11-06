import SampLib.Bernoulli.CoinConditional

/-! # Finite geometric walks

Geometric tails give the probability of hitting the lower endpoint. An exponential
potential supplies a strict exit drift, including the unbiased and one-sided walks.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal BigOperators

namespace SampLib.FiniteGeometricWalk

noncomputable section

def down (t : ℝ) (ht : 0 ≤ t) : unitInterval :=
  ⟨t / (1 + t), div_nonneg ht (by positivity),
    (div_le_one (by positivity)).mpr (by linarith)⟩

@[simp] theorem down_coe (t : ℝ) (ht : 0 ≤ t) :
    (down t ht : ℝ) = t / (1 + t) := rfl

@[simp] theorem one_sub_down (t : ℝ) (ht : 0 ≤ t) :
    1 - (down t ht : ℝ) = 1 / (1 + t) := by
  rw [down_coe]
  field_simp
  ring

def tail (t : ℝ) (N i : ℕ) : ℝ := ∑ j ∈ Finset.Ico i N, t ^ j

def total (t : ℝ) (N : ℕ) : ℝ := ∑ j ∈ Finset.range N, t ^ j

theorem total_pos (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N) :
    0 < total t N := by
  have h := Finset.single_le_sum (f := fun j => t ^ j)
    (fun j _ => pow_nonneg ht j) (Finset.mem_range.mpr hN)
  simp only [pow_zero] at h
  exact lt_of_lt_of_le zero_lt_one h

theorem tail_nonneg (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) : 0 ≤ tail t N i :=
  Finset.sum_nonneg fun j _ => pow_nonneg ht j

theorem tail_le_total (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) : tail t N i ≤ total t N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  · intro j _ _
    exact pow_nonneg ht j

/-- Probability of hitting zero before `N`, starting at `i`. -/
def bias (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N) (i : ℕ) : unitInterval :=
  ⟨tail t N i / total t N, div_nonneg (tail_nonneg t ht N i) (total_pos t ht N hN).le,
    (div_le_one (total_pos t ht N hN)).mpr (tail_le_total t ht N i)⟩

@[simp] theorem bias_zero (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N) :
    bias t ht N hN 0 = 1 := by
  apply Subtype.ext
  change tail t N 0 / total t N = 1
  rw [show tail t N 0 = total t N by simp [tail, total, Nat.Ico_zero_eq_range],
    div_self (total_pos t ht N hN).ne']

@[simp] theorem bias_top (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N) :
    bias t ht N hN N = 0 := by
  apply Subtype.ext
  simp [bias, tail]

private theorem harmonic (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) (hN : 0 < N)
    (hi : 0 < i) (hiN : i < N) :
    (down t ht : ℝ) * (bias t ht N hN (i - 1) : ℝ) +
      (1 - (down t ht : ℝ)) * (bias t ht N hN (i + 1) : ℝ) =
      (bias t ht N hN i : ℝ) := by
  have hd : tail t N (i - 1) = t ^ (i - 1) + tail t N i := by
    simpa only [tail, Nat.sub_add_cancel hi] using
      Finset.sum_eq_sum_Ico_succ_bot (show i - 1 < N by omega) (fun j => t ^ j)
  have hu : tail t N i = t ^ i + tail t N (i + 1) :=
    Finset.sum_eq_sum_Ico_succ_bot hiN (fun j => t ^ j)
  have hp : t ^ i = t * t ^ (i - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hi]
    rw [pow_succ, mul_comm]
  simp only [down_coe, bias]
  field_simp [(total_pos t ht N hN).ne', (show 0 < 1 + t by positivity).ne']
  nlinarith [hd, hu]

def credit (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N)
    (F : Bool → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ := RealCoin.credit (bias t ht N hN i) F

@[simp] theorem credit_zero (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N)
    (F : Bool → ℝ≥0∞) : credit t ht N hN F 0 = F true := by
  simp [credit, RealCoin.credit, RealCoin.pmf]

@[simp] theorem credit_top (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N)
    (F : Bool → ℝ≥0∞) : credit t ht N hN F N = F false := by
  simp [credit, RealCoin.credit, RealCoin.pmf]

/-- The geometric-tail harmonic identity transports arbitrary, possibly infinite, credits. -/
theorem credit_harmonic (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) (hN : 0 < N)
    (hi : 0 < i) (hiN : i < N) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, credit t ht N hN F (if b then i - 1 else i + 1) ∂RealCoin.law (down t ht) =
      credit t ht N hN F i := by
  have hbias : CoinConditional.bias (bias t ht N hN (i - 1))
      (bias t ht N hN (i + 1)) (down t ht) = bias t ht N hN i := by
    apply Subtype.ext
    change (1 - (down t ht : ℝ)) * (bias t ht N hN (i + 1) : ℝ) +
      (down t ht : ℝ) * (bias t ht N hN (i - 1) : ℝ) = _
    linarith [harmonic t ht N i hN hi hiN]
  have h := CoinConditional.expectation_preservation (bias t ht N hN (i - 1))
    (bias t ht N hN (i + 1)) (down t ht) F
  calc
    _ = ∫⁻ b, CoinConditional.firstCredit (bias t ht N hN (i - 1))
        (bias t ht N hN (i + 1)) F b ∂RealCoin.law (down t ht) := by
      apply lintegral_congr
      intro b
      cases b <;> simp [credit, CoinConditional.firstCredit, RealCoin.lintegral_law]
    _ = _ := by
      simpa only [CoinConditional.law, hbias, RealCoin.lintegral_law, credit] using h

/-- Clipping the exponential potential at the absorbing endpoints only improves its drift. -/
def work (t : ℝ) (N i : ℕ) : ℝ :=
  if i = 0 then 0 else (2 * (1 + t)) ^ N - (2 * (1 + t)) ^ i

theorem work_nonneg (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) (hi : i ≤ N) :
    0 ≤ work t N i := by
  unfold work
  split_ifs
  · exact le_rfl
  · exact sub_nonneg.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ 2 * (1 + t)) hi)

@[simp] theorem work_zero (t : ℝ) (N : ℕ) : work t N 0 = 0 := by simp [work]
@[simp] theorem work_top (t : ℝ) (N : ℕ) : work t N N = 0 := by simp [work]

theorem work_drift (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) (hi : 0 < i) (hiN : i < N) :
    (down t ht : ℝ) * work t N (i - 1) +
      (1 - (down t ht : ℝ)) * work t N (i + 1) + 1 ≤ work t N i := by
  let M := 2 * (1 + t)
  have hM : 1 ≤ M := by dsimp [M]; linarith
  have hlo : work t N (i - 1) ≤ M ^ N - M ^ (i - 1) := by
    unfold work
    split_ifs
    · exact sub_nonneg.mpr (pow_le_pow_right₀ hM (by omega))
    · exact le_rfl
  have hq : (1 - (down t ht : ℝ)) * M = 2 := by
    rw [one_sub_down]
    dsimp [M]
    field_simp
  have hp : 1 ≤ M ^ i := one_le_pow₀ hM
  have hd := mul_nonneg (down t ht).2.1 (pow_nonneg (le_trans zero_le_one hM) (i - 1))
  have hu : work t N (i + 1) = M ^ N - M ^ i * M := by
    simp [work, M, pow_succ]
  have hs : work t N i = M ^ N - M ^ i := ite_eq_right (by omega)
  have hweighted := mul_le_mul_of_nonneg_left hlo (down t ht).2.1
  rw [hu, hs]
  nlinarith [mul_assoc (1 - (down t ht : ℝ)) (M ^ i) M]

def stepCredit (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 0 < N)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (i : ℕ) (b : Bool) : ℝ≥0∞ :=
  let j := if b then i - 1 else i + 1
  credit t ht N hN F j + ofReal (work t N j) * δ + 2 * δ

/-- Harmonic output credit and strict work drift fund exactly one amplified continuation. -/
theorem expectation (t : ℝ) (ht : 0 ≤ t) (N i : ℕ) (hN : 0 < N)
    (hi : 0 < i) (hiN : i < N) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) :
    ∫⁻ b, stepCredit t ht N hN F δ i b ∂RealCoin.law (down t ht) ≤
      credit t ht N hN F i + ofReal (work t N i) * δ + δ := by
  have hlo := work_nonneg t ht N (i - 1) (by omega)
  have hup := work_nonneg t ht N (i + 1) (by omega)
  have hstate := work_nonneg t ht N i hiN.le
  have hθ := (down t ht).2.1
  have hq := sub_nonneg.mpr (down t ht).2.2
  have hdrift := work_drift t ht N i hi hiN
  have hslack : ofReal (down t ht : ℝ) * (ofReal (work t N (i - 1)) + 2) +
      ofReal (1 - (down t ht : ℝ)) * (ofReal (work t N (i + 1)) + 2) ≤
      ofReal (work t N i) + 1 := by
    have h := ENNReal.ofReal_le_ofReal (show
        (down t ht : ℝ) * (work t N (i - 1) + 2) +
          (1 - (down t ht : ℝ)) * (work t N (i + 1) + 2) ≤ work t N i + 1 by
      nlinarith)
    rw [ENNReal.ofReal_add (mul_nonneg hθ (by linarith))
        (mul_nonneg hq (by linarith)),
      ENNReal.ofReal_mul hθ, ENNReal.ofReal_mul hq,
      ENNReal.ofReal_add hlo (by norm_num), ENNReal.ofReal_add hup (by norm_num),
      ENNReal.ofReal_add hstate zero_le_one] at h
    norm_num at h ⊢
    exact h
  calc
    _ = (∫⁻ b, credit t ht N hN F (if b then i - 1 else i + 1)
          ∂RealCoin.law (down t ht)) +
        (ofReal (down t ht : ℝ) * (ofReal (work t N (i - 1)) + 2) +
          ofReal (1 - (down t ht : ℝ)) * (ofReal (work t N (i + 1)) + 2)) * δ := by
      simp only [RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf, stepCredit,
        ite_true, Bool.false_eq_true, ite_false]
      ring
    _ ≤ credit t ht N hN F i + (ofReal (work t N i) + 1) * δ := by
      rw [credit_harmonic t ht N i hN hi hiN]
      exact add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul_right hslack δ)
    _ = _ := by ring

/-- Scale ambient slack once; the resulting work coefficient remains fixed during induction. -/
def initialSlack (t : ℝ) (N i : ℕ) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  (ofReal (work t N i) + 1)⁻¹ * ε

theorem initialSlack_pos (t : ℝ) (N i : ℕ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    0 < initialSlack t N i ε := by
  apply ENNReal.mul_pos
  · exact ne_of_gt (ENNReal.inv_pos.mpr (by finiteness))
  · exact ne_of_gt hε

theorem initialSlack_budget (t : ℝ) (N i : ℕ) (ε : ℝ≥0∞) :
    ofReal (work t N i) * initialSlack t N i ε + initialSlack t N i ε = ε := by
  calc
    _ = (ofReal (work t N i) + 1) * initialSlack t N i ε := by ring
    _ = ε := ?_
  simp only [initialSlack]
  rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]

end

end SampLib.FiniteGeometricWalk
