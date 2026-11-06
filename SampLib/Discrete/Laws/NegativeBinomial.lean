import SampLib.Discrete.Laws.Geometric

/-! # Negative-binomial failure counts

The law sums independent geometric failure counts, one per required success.
Its first-trial recurrence lowers the success target or adds one failure.
-/

open scoped ENNReal

namespace SampLib.NegativeBinomial

noncomputable section

open MeasureTheory Measure

/-- Sum of `r` independent geometric failure counts; zero successes return zero. -/
def law (p : unitInterval) : ℕ → Measure ℕ
  | 0 => dirac 0
  | r + 1 => ((law p r).prod (Geometric.law p)).map (fun z => z.2 + z.1)

instance (p : unitInterval) (r : ℕ) : IsProbabilityMeasure (law p r) := by
  induction r with
  | zero => dsimp [law]; infer_instance
  | succ r ih =>
    let := ih
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Expected continuation credit. -/
def credit (p : unitInterval) (r : ℕ) (F : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ n, F n ∂law p r

/-- The remaining credit after observing the first geometric count. -/
def firstCredit (p : unitInterval) (F : ℕ → ℝ≥0∞) (y : ℕ) : ℝ≥0∞ :=
  Geometric.credit p (fun x => F (x + y))

/-- Independence turns the convolution expectation into two successive expectations. -/
theorem credit_succ (p : unitInterval) (r : ℕ) (F : ℕ → ℝ≥0∞) :
    credit p (r + 1) F = credit p r (firstCredit p F) := by
  rw [credit, law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]
  rfl

private theorem convolution (p : unitInterval) (r : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ y, ∫⁻ x, F (x + y) ∂Geometric.law p ∂law p r = ∫⁻ n, F n ∂law p (r + 1) :=
  (credit_succ p r F).symm

/-- An immediate success lowers the success target; a failure adds one count. -/
theorem expectation_step (p : unitInterval) (hp : 0 < (p : ℝ)) (r : ℕ)
    (F : ℕ → ℝ≥0∞) :
    ∫⁻ n, F n ∂law p (r + 1) =
      RealCoin.pmf p true * (∫⁻ n, F n ∂law p r) +
        RealCoin.pmf p false * (∫⁻ n, F (n + 1) ∂law p (r + 1)) := by
  have hp' : p ≠ 0 := by intro h; simp [h] at hp
  have hgeo (y : ℕ) :
      (∫⁻ x, F (x + y) ∂Geometric.law p) =
        RealCoin.pmf p true * F y +
          RealCoin.pmf p false * (∫⁻ x, F (x + y + 1) ∂Geometric.law p) := by
    simpa only [Geometric.law, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false,
      Nat.zero_add, Nat.add_right_comm _ 1] using
      ProbabilityTheory.lintegral_geometricMeasure_succ p hp' (fun x => F (x + y))
  calc
    _ = ∫⁻ y, ∫⁻ x, F (x + y) ∂Geometric.law p ∂law p r := (convolution p r F).symm
    _ = ∫⁻ y, RealCoin.pmf p true * F y +
        RealCoin.pmf p false * (∫⁻ x, F (x + y + 1) ∂Geometric.law p) ∂law p r :=
      lintegral_congr hgeo
    _ = _ := by
      rw [lintegral_add_left (measurable_of_countable _),
        lintegral_const_mul _ (measurable_of_countable _),
        lintegral_const_mul _ (measurable_of_countable _),
        convolution p r (fun n => F (n + 1))]

private theorem geometric_one : Geometric.law 1 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro n
  cases n with
  | zero => simp [Geometric.law, ProbabilityTheory.geometricMeasure_singleton
      (by norm_num : (1 : unitInterval) ≠ 0)]
  | succ n => simp [Geometric.law, ProbabilityTheory.geometricMeasure_singleton
      (by norm_num : (1 : unitInterval) ≠ 0)]

@[simp] theorem law_one (r : ℕ) : law 1 r = Measure.dirac 0 := by
  induction r with
  | zero => rfl
  | succ r IH =>
    rw [law, IH, geometric_one, Measure.dirac_prod_dirac, Measure.map_dirac]
    rfl

end

end SampLib.NegativeBinomial
