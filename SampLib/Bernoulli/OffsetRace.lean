import SampLib.Core.SamplerStep
import SampLib.Common.FactorySyntax
import SampLib.Bernoulli.BernoulliRace
import Samplers.Bernoulli.Rational

/-! # Bernoulli races with rational offsets

Each side samples a uniform rank in three intervals: certain success, a fresh
input coin, or certain failure. Racing the resulting affine coins cancels their
common normalization.
-/

open ProbLang Finset
open ENNReal (ofReal ofReal_div_of_pos)
open scoped ENNReal

namespace SampLib.OffsetRace

noncomputable section

/-- Bias of a certain-success interval followed by an input-coin interval. -/
def affineBias (p : unitInterval) (a s t : ℕ) (ht : 0 < t) (hast : a + s ≤ t) : unitInterval :=
  ⟨((a : ℝ) + s * (p : ℝ)) / t,
    div_nonneg (add_nonneg (Nat.cast_nonneg a)
      (mul_nonneg (Nat.cast_nonneg s) p.2.1)) (Nat.cast_nonneg t),
    (div_le_one (by exact_mod_cast ht)).mpr (by
      have hat : (a : ℝ) + s ≤ t := by exact_mod_cast hast
      calc
        _ ≤ (a : ℝ) + s := by
          nlinarith [mul_le_mul_of_nonneg_left p.2.2 (Nat.cast_nonneg s)]
        _ ≤ _ := hat)⟩

/-- Credit after observing the common uniform rank. -/
def rankCredit (p : unitInterval) (a s : ℕ) (F : Bool → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if k < a then F true else if k < a + s then RealCoin.credit p F else F false

section mathematics

private def categoryCredit (p : unitInterval) (F : Bool → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then F true else if j = 1 then RealCoin.credit p F else F false

/-- The three intervals contribute their widths times their conditional credits. -/
private theorem rank_partition (p : unitInterval) (a s t : ℕ) (hast : a + s ≤ t)
    (F : Bool → ℝ≥0∞) :
    (∑ k ∈ range t, rankCredit p a s F k) =
      a * F true + s * RealCoin.credit p F + (t - (a + s) : ℕ) * F false := by
  have hcategory (k : ℕ) : rankCredit p a s F k =
      categoryCredit p F (WeightedChoice.category [a, s, t - (a + s)] k) := by
    by_cases ha : k < a
    · simp [rankCredit, WeightedChoice.category, categoryCredit, ha]
    · by_cases hs : k < a + s
      · have hsub : k - a < s := by omega
        simp [rankCredit, WeightedChoice.category, categoryCredit, ha, hs, hsub]
      · have hsub : ¬k - a < s := by omega
        simp only [rankCredit, ite_eq_right ha, ite_eq_right hs,
          WeightedChoice.category, ite_eq_right hsub]
        split_ifs <;> simp [categoryCredit]
  simp_rw [hcategory]
  have hsum : [a, s, t - (a + s)].sum = t := by simp; omega
  simpa [hsum, WeightedChoice.weightedSum, categoryCredit, add_assoc] using
    WeightedChoice.rank_partition [a, s, t - (a + s)] (categoryCredit p F)

/-- Uniform interval widths give the affine Bernoulli expectation, for all credits. -/
theorem expectation (p : unitInterval) (a s t : ℕ) (ht : 0 < t) (hast : a + s ≤ t)
    (F : Bool → ℝ≥0∞) :
    (∑ k ∈ range t, rankCredit p a s F k) / t =
      RealCoin.credit (affineBias p a s t ht hast) F := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have htrue : ofReal (affineBias p a s t ht hast : ℝ) =
      ((a : ℝ≥0∞) + s * ofReal (p : ℝ)) / t := by
    rw [affineBias, ofReal_div_of_pos htR,
      ENNReal.ofReal_add (Nat.cast_nonneg a) (mul_nonneg (Nat.cast_nonneg s) p.2.1),
      ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp
  have hfalse : ofReal (1 - (affineBias p a s t ht hast : ℝ)) =
      ((t - (a + s) : ℕ) + s * ofReal (1 - (p : ℝ))) / t := by
    have heq : 1 - (affineBias p a s t ht hast : ℝ) =
        (((t - (a + s) : ℕ) : ℝ) + s * (1 - (p : ℝ))) / t := by
      simp only [affineBias, Nat.cast_sub hast, Nat.cast_add]
      field_simp
      ring
    rw [heq, ofReal_div_of_pos htR,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg s)
        (sub_nonneg.mpr p.2.2)), ENNReal.ofReal_mul (Nat.cast_nonneg s)]
    simp
  rw [rank_partition p a s t hast F]
  simp only [RealCoin.credit, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false,
    htrue, hfalse, ENNReal.div_eq_inv_mul]
  ring

end mathematics

private def total (a b x y : ℕ) : ℕ := a * y + x * b + b * y

private theorem total_pos (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    0 < total a b x y := by
  have hs := Nat.mul_pos hb hy
  unfold total
  omega

private theorem left_bound (a b x y : ℕ) : x * b + b * y ≤ total a b x y := by
  unfold total
  omega

private theorem right_bound (a b x y : ℕ) : a * y + b * y ≤ total a b x y := by
  unfold total
  omega

private def leftBias (q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :=
  affineBias q (x * b) (b * y) (total a b x y) (total_pos a b x y hb hy)
    (left_bound a b x y)

private def rightBias (p : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :=
  affineBias p (a * y) (b * y) (total a b x y) (total_pos a b x y hb hy)
    (right_bound a b x y)

private def normalizer (a b x y : ℕ) : ℝ := (b * y : ℕ) / (total a b x y : ℝ)

private theorem normalizer_pos (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    0 < normalizer a b x y :=
  div_pos (by exact_mod_cast Nat.mul_pos hb hy) (by exact_mod_cast total_pos a b x y hb hy)

private theorem left_coe (q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (leftBias q a b x y hb hy : ℝ) = normalizer a b x y * ((x : ℝ) / y + (q : ℝ)) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have htR : (total a b x y : ℝ) ≠ 0 := by
    exact_mod_cast (total_pos a b x y hb hy).ne'
  change (((x * b : ℕ) : ℝ) + (b * y : ℕ) * (q : ℝ)) / (total a b x y) = _
  simp only [normalizer, Nat.cast_mul]
  field_simp

private theorem right_coe (p : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (rightBias p a b x y hb hy : ℝ) = normalizer a b x y * ((a : ℝ) / b + (p : ℝ)) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  have htR : (total a b x y : ℝ) ≠ 0 := by
    exact_mod_cast (total_pos a b x y hb hy).ne'
  change (((a * y : ℕ) : ℝ) + (b * y : ℕ) * (p : ℝ)) / (total a b x y) = _
  simp only [normalizer, Nat.cast_mul]
  field_simp

private theorem sum_coe (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (leftBias q a b x y hb hy : ℝ) + (rightBias p a b x y hb hy : ℝ) =
      normalizer a b x y * ((a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ)) := by
  rw [left_coe, right_coe]
  ring

/-- Race the two affine coins using their common uniform-rank normalization. -/
def bias (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) : unitInterval :=
  BernoulliRace.bias (leftBias q a b x y hb hy) (rightBias p a b x y hb hy)

/-- The common normalization cancels, leaving the advertised offset ratio. -/
theorem bias_coe (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y) :
    (bias p q a b x y hb hy : ℝ) = ((x : ℝ) / y + (q : ℝ)) /
      ((a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ)) := by
  change (leftBias q a b x y hb hy : ℝ) /
    ((leftBias q a b x y hb hy : ℝ) + (rightBias p a b x y hb hy : ℝ)) = _
  rw [sum_coe, left_coe, mul_div_mul_left _ _ (normalizer_pos a b x y hb hy).ne']

private theorem race_pos (p q : unitInterval) (a b x y : ℕ) (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ)) :
    0 < (leftBias q a b x y hb hy : ℝ) + (rightBias p a b x y hb hy : ℝ) := by
  rw [sum_coe]
  exact mul_pos (normalizer_pos a b x y hb hy) h

private theorem race_open {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.bernoulliRace = Occil.bernoulliRace :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem race_close {rT : Type _} (k : ℕ) (v : Var) :
    Exp.closeRec k v (Occil.bernoulliRace : Exp rT) = Occil.bernoulliRace :=
  Exp.closeRec_fresh v _ k (by
    simp [Occil.bernoulliRace, Exp.fv, FairCoin.fairCoin_fv])

private theorem nonpositive_test (n : ℕ) (hn : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast Nat.not_le.mpr hn)

private def source {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.offsetRace, .lam (by is_lc), by is_lc⟩

private theorem source_fst {rT : Type _} :
    (source (rT := rT)).fst = Occil.FactoryExtra.offsetRace := rfl

private def rankBody {rT : Type _} (coin : Val rT) (a s : ℕ) : Exp rT :=
  .cond (.binop .lt (.bvar 0) (.lit (.int a))) (.lit (.bool true))
    (.cond (.binop .lt (.bvar 0) (.binop .plus (.lit (.int a)) (.lit (.int s))))
      (.app coin.fst (.lit .unit)) (.lit (.bool false)))

private def callback {rT : Type _} (coin : Val rT) (a s t : ℕ) : Val rT :=
  ⟨.lam (.app (.lam (rankBody coin a s)) pl(&Occil.uniformInt #int (t : ℤ))),
    .lam (by unfold rankBody; is_lc), by unfold rankBody; is_lc⟩

private theorem lt_test (k n : ℕ) : decide ((k : ℤ) < n) = decide (k < n) := by
  simp only [Int.ofNat_lt]

section specification

open FactorySyntax
open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The callback's three branches execute the interval expectation literally. -/
private theorem callback_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (a s t : ℕ) (ht : 0 < t) (hast : a + s ≤ t) :
    IsDistSpec (GF := GF) E pl(&(callback coin a s t).fst #())
      (RealCoin.law (affineBias p a s t ht hast)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    simp only [UniformInt.uniformInt_openRec]
    twp_bind pl(&Occil.uniformInt #int (t : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply UniformInt.twp_uniformInt E t ht (rankCredit p a s F)
      rw [expectation p a s t ht hast F, ← RealCoin.lintegral_law]
      iexact Hcredit
    iintro %v ⟨%k, %hv, %hk, Hcredit⟩
    subst v
    simp [rankBody, Exp.openRec]
    twp_pure
    twp_pures
    by_cases ha : k < a
    · rw [lt_test, decide_eq_true ha]
      twp_pures
      twp_value
      imodintro
      iexists true
      isimp only [rankCredit, ite_eq_left ha] at Hcredit
      iframe Hcredit
      itrivial
    · rw [lt_test, decide_eq_false ha]
      twp_pures
      by_cases hs : k < a + s
      · rw [← Nat.cast_add, lt_test, decide_eq_true hs]
        twp_pures
        isimp only [rankCredit, ite_eq_right ha, ite_eq_left hs,
          ← RealCoin.lintegral_law] at Hcredit
        iapply hcoin.spec F (measurable_of_countable F) $$ Hcredit
      · rw [← Nat.cast_add, lt_test, decide_eq_false hs]
        twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [rankCredit, ite_eq_right ha, ite_eq_right hs] at Hcredit
        iframe Hcredit
        itrivial

/-- Construct the two affine callbacks and invoke the verified Bernoulli race. -/
theorem twp_offsetRace (E : CoPset) (p q : unitInterval) (a b x y : ℕ)
    (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ))
    (pcoin qcoin : Val rT)
    (hpcoin : IsDistSpec (GF := GF) E pl(&pcoin.fst #()) (RealCoin.law p) Val.bool)
    (hqcoin : IsDistSpec (GF := GF) E pl(&qcoin.fst #()) (RealCoin.law q) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂RealCoin.law (bias p q a b x y hb hy)) -∗
      tglWp E pl(&Occil.FactoryExtra.offsetRace &pcoin.fst &qcoin.fst
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
        (fun v : Val rT => iprop(∃ z : Bool, ⌜v = Val.bool z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  rw [← source_fst]
  iterate 7 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.close, Exp.closeRec,
    Exp.ofVal, Var.internal.injEq, ProbLang.openRec_val_fst, race_open, race_close,
    UniformInt.uniformInt_openRec, UniformInt.uniformInt_closeRec])
  twp_pures
  simp only [nonpositive_test b hb, nonpositive_test y hy, Bool.or_false]
  iterate 12 (twp_step; simp -failIfUnchanged [Exp.open', Exp.openRec, Exp.ofVal,
    ProbLang.openRec_val_fst, race_open, UniformInt.uniformInt_openRec])
  simp only [← Nat.cast_mul, ← Nat.cast_add]
  isimp only [bias] at Hcredit
  have hrace := BernoulliRace.bernoulliRace_distSpec (GF := GF) E
    (leftBias q a b x y hb hy) (rightBias p a b x y hb hy) (race_pos p q a b x y hb hy h)
    (callback qcoin (x * b) (b * y) (total a b x y))
    (callback pcoin (a * y) (b * y) (total a b x y))
    (callback_distSpec E q qcoin hqcoin (x * b) (b * y) (total a b x y)
      (total_pos a b x y hb hy) (left_bound a b x y))
    (callback_distSpec E p pcoin hpcoin (a * y) (b * y) (total a b x y)
      (total_pos a b x y hb hy) (right_bound a b x y))
  simp only [callback, rankBody, total] at hrace
  iapply hrace.spec F (measurable_of_countable F) $$ Hcredit

/-- Full nonnegative rational offsets, positive denominators, and positive total exit mass. -/
theorem offsetRace_distSpec (E : CoPset) (p q : unitInterval) (a b x y : ℕ)
    (hb : 0 < b) (hy : 0 < y)
    (h : 0 < (a : ℝ) / b + (p : ℝ) + (x : ℝ) / y + (q : ℝ))
    (pcoin qcoin : Val rT)
    (hpcoin : IsDistSpec (GF := GF) E pl(&pcoin.fst #()) (RealCoin.law p) Val.bool)
    (hqcoin : IsDistSpec (GF := GF) E pl(&qcoin.fst #()) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.offsetRace &pcoin.fst &qcoin.fst
      #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
      (RealCoin.law (bias p q a b x y hb hy)) Val.bool where
  spec F _ := wand_entails (twp_offsetRace E p q a b x y hb hy h pcoin qcoin hpcoin hqcoin F)

end specification

end

end SampLib.OffsetRace
