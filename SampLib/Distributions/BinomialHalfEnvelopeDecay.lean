module

public import SampLib.Distributions.BinomialHalfEnvelopeCentral
public import SampLib.Distributions.HazardProduct

@[expose] public section

/-! # Geometric decay of half-binomial blocks

The adjacent binomial ratios decrease away from the center. Across one
square-root-width block, their cumulative hazard is at least one. The reciprocal
survival bound therefore pays for each successive factor of two in the proposal.
-/

open Finset
open SampLib.AbsorbingChain

namespace SampLib.BinomialHalfEnvelope

noncomputable section

/-- Adjacent coefficient ratio, continued by zero beyond the support. -/
def adjacentRatio (m j : ℕ) : ℝ := (m - j : ℕ) / (m + j + 1 : ℝ)

theorem adjacentRatio_mem (m j : ℕ) : adjacentRatio m j ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨by unfold adjacentRatio; positivity, ?_⟩
  apply (div_le_one (by positivity : (0 : ℝ) < m + j + 1)).mpr
  have h : ((m - j : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m j
  linarith [Nat.cast_nonneg (α := ℝ) j]

theorem adjacentRatio_antitone (m : ℕ) : Antitone (adjacentRatio m) := by
  intro i j hij
  have hnum : ((m - j : ℕ) : ℝ) ≤ (m - i : ℕ) := by
    exact_mod_cast Nat.sub_le_sub_left hij m
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith))

/-- The upper half of one symmetric binomial row. -/
def upperCoefficient (m j : ℕ) : ℝ := Nat.choose (2 * m) (m + j)

theorem upperCoefficient_succ (m j : ℕ) :
    upperCoefficient m (j + 1) = upperCoefficient m j * adjacentRatio m j := by
  unfold upperCoefficient adjacentRatio
  rw [← mul_div_assoc]
  apply (eq_div_iff (by positivity : (m + j + 1 : ℝ) ≠ 0)).mpr
  have h := Nat.choose_succ_right_eq (2 * m) (m + j)
  rw [show 2 * m - (m + j) = m - j by omega] at h
  exact_mod_cast h

private theorem survival_succ_right (q : ℕ → ℝ) (start depth : ℕ) :
    realSurvival q start (depth + 1) = realSurvival q start depth * q (start + depth) := by
  induction depth generalizing start with
  | zero => simp [realSurvival]
  | succ depth IH =>
    rw [realSurvival, IH, realSurvival]
    rw [show start + 1 + depth = start + (depth + 1) by omega]
    ring

private theorem survival_append (q : ℕ → ℝ) (start n k : ℕ) :
    realSurvival q start (n + k) = realSurvival q start n * realSurvival q (start + n) k := by
  induction n generalizing start with
  | zero => simp [realSurvival]
  | succ n IH =>
    rw [show n + 1 + k = n + k + 1 by omega, realSurvival, IH, realSurvival]
    rw [show start + 1 + n = start + (n + 1) by omega]
    ring

theorem upperCoefficient_eq_survival (m j : ℕ) :
    upperCoefficient m j = (Nat.centralBinom m : ℝ) * realSurvival (adjacentRatio m) 0 j := by
  induction j with
  | zero => simp [upperCoefficient, Nat.centralBinom, realSurvival]
  | succ j IH =>
    rw [upperCoefficient_succ, IH, survival_succ_right, Nat.zero_add]
    ring

private theorem survival_antitone_depth (m : ℕ) :
    Antitone (realSurvival (adjacentRatio m) 0) := by
  apply antitone_nat_of_succ_le
  intro j
  rw [survival_succ_right, Nat.zero_add]
  simpa using mul_le_mul_of_nonneg_left (adjacentRatio_mem m j).2
    (realSurvival_mem _ (adjacentRatio_mem m) 0 j).1

private theorem survival_antitone_start (m depth : ℕ) :
    Antitone (fun start => realSurvival (adjacentRatio m) start depth) := by
  induction depth with
  | zero => intro i j _; simp [realSurvival]
  | succ depth IH =>
    intro i j hij
    simp only [realSurvival]
    exact mul_le_mul (adjacentRatio_antitone m hij) (IH (Nat.add_le_add_right hij 1))
      (realSurvival_mem _ (adjacentRatio_mem m) (j + 1) depth).1 (adjacentRatio_mem m i).1

private theorem sum_odds (w : ℕ) : (∑ i ∈ range w, (2 * i + 1 : ℝ)) = (w : ℝ) ^ 2 := by
  induction w with
  | zero => simp
  | succ w IH => rw [sum_range_succ, IH]; push_cast; ring

/-- Sum the lower bounds `(2i+1)/(m+w)` on one complete block's hazards. -/
theorem block_hazard_sum {m w : ℕ} (hwm : w ≤ m) :
    (w : ℝ) ^ 2 / (m + w : ℝ) ≤ ∑ i ∈ range w, (1 - adjacentRatio m i) := by
  rw [← sum_odds, sum_div]
  apply sum_le_sum
  intro i hi
  have hiw : i < w := mem_range.mp hi
  have him : i ≤ m := (Nat.le_of_lt hiw).trans hwm
  have hden : (0 : ℝ) < m + i + 1 := by positivity
  have hstep : 1 - adjacentRatio m i = (2 * i + 1 : ℝ) / (m + i + 1 : ℝ) := by
    unfold adjacentRatio
    rw [Nat.cast_sub him]
    field_simp
    ring
  rw [hstep]
  apply div_le_div_of_nonneg_left (by positivity) hden
  have : (i + 1 : ℝ) ≤ w := by exact_mod_cast hiw
  linarith

/-- A square-root-width block loses at least half its starting coefficient. -/
theorem initial_block_le_half {m : ℕ} (hw : width (2 * m) ≤ m) :
    realSurvival (adjacentRatio m) 0 (width (2 * m)) ≤ 1 / 2 := by
  have hwidth : (2 * m : ℝ) < (width (2 * m) : ℝ) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (2 * m)
  have hwm : (width (2 * m) : ℝ) ≤ m := by exact_mod_cast hw
  have hden : (0 : ℝ) < m + width (2 * m) := by
    have := width_pos (2 * m)
    positivity
  have hsum : 1 ≤ ∑ i ∈ range (width (2 * m)), (1 - adjacentRatio m i) := by
    apply le_trans _ (block_hazard_sum hw)
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have h := realSurvival_bound _ (adjacentRatio_mem m) 0 (width (2 * m))
  simp only [Nat.zero_add] at h
  have hs := (realSurvival_mem _ (adjacentRatio_mem m) 0 (width (2 * m))).1
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hsum)]

/-- Every later complete block has at most half its predecessor's mass. -/
theorem block_survival_bound {m : ℕ} (hw : width (2 * m) ≤ m) (b : ℕ) :
    realSurvival (adjacentRatio m) 0 (b * width (2 * m)) ≤ (1 / 2 : ℝ) ^ b := by
  induction b with
  | zero => simp [realSurvival]
  | succ b IH =>
    rw [Nat.succ_mul, survival_append]
    have hblock : realSurvival (adjacentRatio m) (b * width (2 * m)) (width (2 * m)) ≤
        (1 / 2 : ℝ) :=
      (survival_antitone_start m (width (2 * m)) (Nat.zero_le _)).trans
        (initial_block_le_half hw)
    simpa only [pow_succ, Nat.zero_add] using mul_le_mul IH hblock
      (realSurvival_mem _ (adjacentRatio_mem m) (b * width (2 * m)) (width (2 * m))).1
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ b)

/-- Invalid distant blocks need no special small-`n` exception. -/
theorem upperCoefficient_block_bound (m b d : ℕ)
    (hbd : b * width (2 * m) ≤ d) (hd : d ≤ m) :
    upperCoefficient m d ≤ (Nat.centralBinom m : ℝ) * (1 / 2 : ℝ) ^ b := by
  by_cases hw : width (2 * m) ≤ m
  · rw [upperCoefficient_eq_survival]
    apply mul_le_mul_of_nonneg_left
      ((survival_antitone_depth m hbd).trans (block_survival_bound hw b)) (by positivity)
  · have hb : b = 0 := by
      by_contra hb
      have hmul : width (2 * m) ≤ b * width (2 * m) :=
        Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hb)
      omega
    subst b
    simp only [pow_zero, mul_one, upperCoefficient]
    exact_mod_cast Nat.choose_le_centralBinom (m + d) m

/-- Pointwise domination by the source's dyadic block envelope. -/
theorem point_envelope (m b d : ℕ) (hbd : b * width (2 * m) ≤ d) (hd : d ≤ m) :
    upperCoefficient m d * width (2 * m) * (2 : ℝ) ^ b ≤ 4 * (2 : ℝ) ^ (2 * m) := by
  have hcancel : (1 / 2 : ℝ) ^ b * (2 : ℝ) ^ b = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = upperCoefficient m d * (width (2 * m) * (2 : ℝ) ^ b) := by ring
    _ ≤ ((Nat.centralBinom m : ℝ) * (1 / 2 : ℝ) ^ b) *
        (width (2 * m) * (2 : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_right (upperCoefficient_block_bound m b d hbd hd) (by positivity)
    _ = (Nat.centralBinom m : ℝ) * width (2 * m) * ((1 / 2 : ℝ) ^ b * (2 : ℝ) ^ b) := by ring
    _ = (Nat.centralBinom m : ℝ) * width (2 * m) := by rw [hcancel, mul_one]
    _ ≤ _ := central_envelope m

end

end SampLib.BinomialHalfEnvelope
