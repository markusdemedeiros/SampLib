import SampLib.Bernoulli.TwoCoinPower
import SampLib.Latent.UniformBagCoin
import SampLib.Discrete.Geometric

/-! # Power-factory credits conditional on a shared latent uniform

The input coin remains independent of the shared uniform. Conditioning on that
uniform gives the same first-exit recurrence, while posterior integration keeps
all dependence in the exponent oracle and output continuation.
-/

open ProbLang MeasureTheory
open scoped ENNReal

namespace SampLib.LatentPower

noncomputable section

def credit (p : unitInterval) (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (n : ℕ) (u : ℝ) : ℝ≥0∞ := FractionalPower.tailCredit p (φ u) (fun b => G b u) n

def exponentKernel (p : unitInterval) (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (n : ℕ) (b : Bool) (u : ℝ) : ℝ≥0∞ :=
  TwoCoinPower.exponentCredit n (fun bit => G bit u) (credit p φ G (n + 1) u) b

def inputKernel (p : unitInterval) (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (n : ℕ) (b : Bool) (u : ℝ) : ℝ≥0∞ :=
  TwoCoinPower.firstCredit (φ u) n (fun bit => G bit u) (credit p φ G (n + 1) u) b

theorem measurable_continue (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    (n : ℕ) : Measurable (fun u => FractionalPower.continueProb p (φ u) n) := by
  unfold FractionalPower.continueProb
  fun_prop

theorem measurable_survival (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    (n depth : ℕ) :
    Measurable (fun u =>
      AbsorbingChain.survival (FractionalPower.continueProb p (φ u)) n depth) := by
  induction depth generalizing n with
  | zero => simpa only [AbsorbingChain.survival_zero] using measurable_const
  | succ depth ih =>
    simp only [AbsorbingChain.survival_succ]
    exact (measurable_continue p hφ n).mul (ih (n + 1))

theorem measurable_exit (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) :
    Measurable (fun u => FractionalPower.exitCredit p (φ u) (fun b => G b u) n) := by
  have ht := hG true
  have hf := hG false
  unfold FractionalPower.exitCredit
  fun_prop

theorem measurable_credit (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) :
    Measurable (credit p φ G n) := by
  unfold credit FractionalPower.tailCredit
  apply Measurable.tsum
  intro depth
  exact (measurable_survival p hφ n depth).mul (measurable_exit p hφ hG (n + depth))

theorem measurable_exponentKernel (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) (b : Bool) :
    Measurable (exponentKernel p φ G n b) := by
  change Measurable (fun u => exponentKernel p φ G n b u)
  cases b
  · simpa only [exponentKernel, TwoCoinPower.exponentCredit, CoinProduct.firstCredit,
      FractionalPower.hazardCredit, Bool.false_eq_true, ite_false] using
      measurable_credit p hφ hG (n + 1)
  · have hgate : ∀ bit : Bool, Measurable (fun u =>
        FractionalPower.hazardCredit (fun b => G b u) (credit p φ G (n + 1) u) bit) := by
      intro bit
      cases bit
      · simpa only [FractionalPower.hazardCredit, Bool.false_eq_true, ite_false] using
          measurable_credit p hφ hG (n + 1)
      · simpa only [FractionalPower.hazardCredit, ite_true] using hG false
    have h := LatentBernoulli.measurable_kernel
      (φ := fun _ => FractionalPower.hazardBias 1 n) measurable_const hgate
    convert h using 1
    funext u
    simp only [exponentKernel, TwoCoinPower.exponentCredit, CoinProduct.firstCredit,
      ite_true, RealCoin.lintegral_law, LatentBernoulli.kernel]

theorem measurable_inputKernel (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) (b : Bool) :
    Measurable (inputKernel p φ G n b) := by
  change Measurable (fun u => inputKernel p φ G n b u)
  cases b
  · have h := LatentBernoulli.measurable_kernel hφ (measurable_exponentKernel p hφ hG n)
    convert h using 1
    funext u
    rfl
  · simpa only [inputKernel, TwoCoinPower.firstCredit, ite_true] using hG true

/-- Pointwise first-round conditioning preserves the remaining output expectation. -/
theorem pointwise_expectation (p : unitInterval) (φ : ℝ → unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) (u : ℝ) :
    RealCoin.credit p (fun b => inputKernel p φ G n b u) = credit p φ G n u := by
  have h := TwoCoinPower.round_expectation p (φ u) n (fun b => G b u)
    (credit p φ G (n + 1) u)
  rw [RealCoin.lintegral_law] at h
  exact h.trans (FractionalPower.tailCredit_succ p (φ u) (fun b => G b u) n).symm

/-- A fresh input coin commutes with posterior averaging over the exponent oracle. -/
theorem posterior_expectation (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    (q : List Bool) {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) :
    RealCoin.credit p (fun b => DyadicPosterior.credit q (inputKernel p φ G n b)) =
      DyadicPosterior.credit q (credit p φ G n) := by
  rw [← LatentBernoulli.credit_fixed_bias q p _ (measurable_inputKernel p hφ hG n)]
  unfold LatentBernoulli.credit LatentBernoulli.kernel DyadicPosterior.credit
  apply lintegral_congr
  intro u
  exact pointwise_expectation p φ G n u

def baseBudget (p : unitInterval) (φ : ℝ → unitInterval) (q : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) (ε : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  DyadicPosterior.credit q (inputKernel p φ G n b) +
    if b then RealCoin.pmf p true * ε else (Geometric.terminationFactor p : ℝ≥0∞) * ε

theorem terminationFactor_gt_one (p : unitInterval) (hp : 0 < (p : ℝ)) :
    1 < Geometric.terminationFactor p := by
  change 1 < 1 + unitInterval.toNNReal p
  exact lt_add_of_pos_right _ (by exact_mod_cast hp)

/-- Posterior averaging preserves the output law and pays one unit of retry slack. -/
theorem expectation (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    (q : List Bool) {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b))
    (n : ℕ) (ε : ℝ≥0∞) :
    ∫⁻ b, baseBudget p φ q G n ε b ∂RealCoin.law p =
      DyadicPosterior.credit q (credit p φ G n) + ε := by
  have hk : (Geometric.terminationFactor p : ℝ≥0∞) = 1 + RealCoin.pmf p true := by
    simp [Geometric.terminationFactor, ENNReal.coe_nnreal_eq, RealCoin.pmf,
      ENNReal.ofReal_add zero_le_one p.2.1]
  have hterm : RealCoin.pmf p true * RealCoin.pmf p true +
      RealCoin.pmf p false * Geometric.terminationFactor p = 1 := by
    calc
      _ = RealCoin.pmf p true * (RealCoin.pmf p true + RealCoin.pmf p false) +
          RealCoin.pmf p false := by rw [hk]; ring
      _ = 1 := by simp only [RealCoin.pmf_sum, mul_one]
  rw [RealCoin.lintegral_law]
  calc
    _ = RealCoin.credit p (fun b => DyadicPosterior.credit q (inputKernel p φ G n b)) +
        (RealCoin.pmf p true * RealCoin.pmf p true +
          RealCoin.pmf p false * Geometric.terminationFactor p) * ε := by
      simp only [RealCoin.credit, baseBudget, Bool.false_eq_true, ite_false, ite_true]
      ring
    _ = _ := by rw [posterior_expectation p hφ q hG n, hterm, one_mul]

@[simp] theorem input_true (p : unitInterval) (φ : ℝ → unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) : inputKernel p φ G n true = G true := rfl

@[simp] theorem input_false (p : unitInterval) (φ : ℝ → unitInterval) (q : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) :
    DyadicPosterior.credit q (inputKernel p φ G n false) =
      LatentBernoulli.credit q φ (exponentKernel p φ G n) := rfl

@[simp] theorem exponent_false (p : unitInterval) (φ : ℝ → unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) :
    exponentKernel p φ G n false = credit p φ G (n + 1) := rfl

def gateKernel (p : unitInterval) (φ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞)
    (n : ℕ) (b : Bool) (u : ℝ) : ℝ≥0∞ :=
  FractionalPower.hazardCredit (fun bit => G bit u) (credit p φ G (n + 1) u) b

theorem measurable_gateKernel (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) (b : Bool) :
    Measurable (gateKernel p φ G n b) := by
  change Measurable (fun u => gateKernel p φ G n b u)
  cases b
  · simpa only [gateKernel, FractionalPower.hazardCredit, Bool.false_eq_true, ite_false] using
      measurable_credit p hφ hG (n + 1)
  · simpa only [gateKernel, FractionalPower.hazardCredit, ite_true] using hG false

theorem gate_expectation (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ)
    (q : List Bool) {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (n : ℕ) :
    ∫⁻ b, DyadicPosterior.credit q (gateKernel p φ G n b)
      ∂RealCoin.law (FractionalPower.hazardBias 1 n) =
        DyadicPosterior.credit q (exponentKernel p φ G n true) := by
  rw [RealCoin.lintegral_law,
    ← LatentBernoulli.credit_fixed_bias q (FractionalPower.hazardBias 1 n) _
      (measurable_gateKernel p hφ hG n)]
  unfold LatentBernoulli.credit LatentBernoulli.kernel DyadicPosterior.credit
  apply lintegral_congr
  intro u
  simp only [exponentKernel, TwoCoinPower.exponentCredit, CoinProduct.firstCredit,
    ite_true, RealCoin.lintegral_law, gateKernel]

@[simp] theorem gate_true (p : unitInterval) (φ : ℝ → unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) : gateKernel p φ G n true = G false := rfl

@[simp] theorem gate_false (p : unitInterval) (φ : ℝ → unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (n : ℕ) : gateKernel p φ G n false = credit p φ G (n + 1) := rfl

/-- The initial conditional law is Bernoulli with success bias `p^(φ(u))`. -/
theorem credit_zero (p : unitInterval) (hp : 0 < (p : ℝ)) (φ : ℝ → unitInterval)
    (q : List Bool) (G : Bool → ℝ → ℝ≥0∞) :
    DyadicPosterior.credit q (credit p φ G 0) =
      LatentBernoulli.credit q (fun u => FractionalPower.powerBias p (φ u)) G := by
  unfold DyadicPosterior.credit credit LatentBernoulli.credit LatentBernoulli.kernel
  apply lintegral_congr
  intro u
  exact FractionalPower.tailCredit_zero p (φ u) (Or.inl hp) (fun b => G b u)

theorem measurable_powerBias (p : unitInterval) {φ : ℝ → unitInterval} (hφ : Measurable φ) :
    Measurable (fun u => FractionalPower.powerBias p (φ u)) := by
  unfold FractionalPower.powerBias
  fun_prop

end

end SampLib.LatentPower
