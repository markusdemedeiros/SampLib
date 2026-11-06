import SampLib.Bernoulli.Laws.Linear2014Parameters
import SampLib.Bernoulli.Laws.Linear2014Step

/-! # Two levels of termination credit for the geometric-jump factory

The power harmonicity pays every output continuation. Uniform escape funds
recursion within one stage; the boundary selector funds recursion to the next.
-/

open Set MeasureTheory
open ENNReal (ofReal)
open scoped ENNReal NNReal

namespace SampLib.Linear2014

noncomputable section

namespace Parameters

variable {p : unitInterval} (σ : Parameters p)

def escape : ℝ := Linear2014Jump.escape p σ.jumpBias σ.numerator.toNat

theorem escape_pos : 0 < σ.escape :=
  Linear2014Jump.escape_pos p σ.jumpBias σ.input_lt_one σ.jumpBias_lt_one _

theorem escape_le_one : σ.escape ≤ 1 := by
  have htail : (1 - (σ.jumpBias : ℝ)) ^ σ.numerator.toNat ≤ 1 :=
    pow_le_one₀ (sub_nonneg.mpr σ.jumpBias.2.2) (by linarith [σ.jumpBias.2.1])
  exact (mul_le_mul_of_nonneg_left htail (sub_nonneg.mpr p.2.2)).trans
    (by simpa using sub_le_self (1 : ℝ) p.2.1)

def terminationFactor : ℝ≥0 := ⟨1 + σ.escape, by have := σ.escape_pos; positivity⟩

theorem one_lt_terminationFactor : 1 < σ.terminationFactor := by
  change (1 : ℝ) < 1 + σ.escape
  linarith [σ.escape_pos]

private theorem escape_budget : ofReal (1 - σ.escape) * σ.terminationFactor ≤ 1 := by
  rw [ENNReal.coe_nnreal_eq σ.terminationFactor]
  change ofReal (1 - σ.escape) * ofReal (1 + σ.escape) ≤ 1
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr σ.escape_le_one)]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
    (show (1 - σ.escape) * (1 + σ.escape) ≤ 1 by
      nlinarith [sq_nonneg σ.escape])

def ordinary (n : ℕ) : Prop := 0 < n ∧ (n : ℤ) * σ.denominator < σ.numerator

instance (n : ℕ) : Decidable (σ.ordinary n) := by
  unfold ordinary
  infer_instance

private theorem ordinary_cast (n : ℕ) :
    σ.ordinary n ↔ 0 < n ∧ n * σ.denominator.toNat < σ.numerator.toNat := by
  have hN := Int.toNat_of_nonneg σ.numerator_pos.le
  have hD := Int.toNat_of_nonneg σ.denominator_pos.le
  unfold ordinary
  constructor <;> rintro ⟨hn, h⟩ <;> refine ⟨hn, ?_⟩
  · rw [← hD, ← hN] at h
    exact_mod_cast h
  · rw [← hD, ← hN]
    exact_mod_cast h

/-- The selector's accepted branch passes doubled credit to the next stage. -/
def boundaryCredit (n : ℕ) (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) (z : Bool) : ℝ≥0∞ :=
  if z then IterateCoin.credit σ.next.bias n F + 2 * δ else F false

private theorem boundary_expectation (n : ℕ) (hn : σ.numerator ≤ (n : ℤ) * σ.denominator)
    (F : Bool → ℝ≥0∞) (δ : ℝ≥0∞) :
    (∫⁻ z, σ.boundaryCredit n F δ z ∂RealCoin.law (σ.selector n)) ≤
      IterateCoin.credit σ.bias n F + δ := by
  have hmix : CoinConditional.bias (IterateCoin.bias σ.next.bias n) 0 (σ.selector n) =
      IterateCoin.bias σ.bias n := by
    apply Subtype.ext
    simp only [CoinConditional.bias, Set.Icc.convexComb, Set.Icc.coe_zero,
      IterateCoin.bias, mul_zero, zero_add, σ.next_bias, σ.selector_coe, mul_pow]
    field_simp [show 2 + σ.margin ≠ 0 by have := σ.margin_pos; linarith]
  have hcredit : (∫⁻ z, (if z then IterateCoin.credit σ.next.bias n F else F false)
      ∂RealCoin.law (σ.selector n)) = IterateCoin.credit σ.bias n F := by
    have h := CoinConditional.expectation_preservation
      (IterateCoin.bias σ.next.bias n) 0 (σ.selector n) F
    simpa [CoinConditional.firstCredit, CoinConditional.law, hmix,
      RealCoin.lintegral_law, IterateCoin.credit, RealCoin.credit, RealCoin.pmf] using h
  have hq : ofReal (σ.selector n : ℝ) * 2 ≤ 1 := by
    have h := Linear2014Jump.boosted_boundary σ.margin σ.margin_pos.le n (σ.crossing n hn)
    rw [← σ.selector_coe] at h
    have hr : (σ.selector n : ℝ) * 2 ≤ 1 := by linarith
    simpa only [ENNReal.ofReal_mul (σ.selector n).2.1, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal hr
  calc
    _ = (∫⁻ z, (if z then IterateCoin.credit σ.next.bias n F else F false)
        ∂RealCoin.law (σ.selector n)) + (ofReal (σ.selector n : ℝ) * 2) * δ := by
      simp only [boundaryCredit, RealCoin.lintegral_law, RealCoin.credit, RealCoin.pmf,
        ite_true, Bool.false_eq_true, ite_false]
      ring
    _ ≤ IterateCoin.credit σ.bias n F + δ := by
      rw [hcredit]
      gcongr
      simpa only [mul_comm, one_mul, mul_one] using mul_le_mul_right hq δ

/-- Credit after the sampled jump, before its three deterministic branches. -/
def continuation (n : ℕ) (F : Bool → ℝ≥0∞) (δ ζ : ℝ≥0∞) : ℝ≥0∞ :=
  if n = 0 then F true else
  if σ.ordinary n then IterateCoin.credit σ.bias n F + δ + σ.terminationFactor * ζ else
    ∫⁻ z, σ.boundaryCredit n F δ z ∂RealCoin.law (σ.selector n)

private theorem continuation_bound (n : ℕ) (F : Bool → ℝ≥0∞) (δ ζ : ℝ≥0∞) :
    σ.continuation n F δ ζ ≤ IterateCoin.credit σ.bias n F + δ +
      Linear2014Jump.ordinary σ.numerator.toNat σ.denominator.toNat n *
        σ.terminationFactor * ζ := by
  by_cases hn : n = 0
  · subst n
    simp [continuation, IterateCoin.credit_zero, Linear2014Jump.ordinary]
  · by_cases ho : σ.ordinary n
    · simp [continuation, hn, ho, Linear2014Jump.ordinary, (σ.ordinary_cast n).mp ho]
    · have hc : σ.numerator ≤ (n : ℤ) * σ.denominator := by
        have hn' := Nat.pos_of_ne_zero hn
        simp only [ordinary, hn', true_and] at ho
        omega
      have hnot := (not_congr (σ.ordinary_cast n)).mp ho
      simpa only [continuation, ite_eq_right hn, ite_eq_right ho, Linear2014Jump.ordinary,
        ite_eq_right hnot, zero_mul, add_zero] using
        σ.boundary_expectation n hc F δ

/-- Power conservation and uniform stage escape fund both recursive continuations. -/
theorem expectation (s : ℕ) (hs : 0 < s) (F : Bool → ℝ≥0∞) (δ ζ : ℝ≥0∞) :
    (∫⁻ n, σ.continuation n F δ ζ ∂Linear2014Jump.law p σ.jumpBias s) ≤
      IterateCoin.credit σ.bias s F + δ + ζ := by
  calc
    _ ≤ ∫⁻ n, IterateCoin.credit σ.bias n F + δ +
        Linear2014Jump.ordinary σ.numerator.toNat σ.denominator.toNat n *
          σ.terminationFactor * ζ ∂Linear2014Jump.law p σ.jumpBias s :=
      lintegral_mono (fun n => σ.continuation_bound n F δ ζ)
    _ = IterateCoin.credit σ.bias s F + δ +
        (∫⁻ n, Linear2014Jump.ordinary σ.numerator.toNat σ.denominator.toNat n
          ∂Linear2014Jump.law p σ.jumpBias s) * σ.terminationFactor * ζ := by
      rw [lintegral_add_left (measurable_of_countable _),
        lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const, measure_univ, mul_one]
      rw [lintegral_mul_const _ (measurable_of_countable _),
        lintegral_mul_const _ (measurable_of_countable _),
        Linear2014Jump.credit_expectation p σ.jumpBias σ.bias σ.jumpBias_pos
          σ.jump_relation s hs F]
    _ ≤ IterateCoin.credit σ.bias s F + δ +
        ofReal (1 - σ.escape) * σ.terminationFactor * ζ := by
      gcongr
      exact Linear2014Jump.ordinary_bound p σ.jumpBias σ.jumpBias_pos _ _ s
        (by have := σ.denominator_pos; omega)
    _ ≤ _ := by
      gcongr
      simpa only [mul_comm, one_mul, mul_one] using mul_le_mul_right σ.escape_budget ζ

end Parameters

end

end SampLib.Linear2014
