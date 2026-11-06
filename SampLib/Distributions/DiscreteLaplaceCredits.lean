import SampLib.Distributions.DiscreteLaplace

/-! # Continuation credits for the discrete-Laplace rejection loop

Acceptance of the remainder is tested before the whole part and sign are drawn.
Tonelli's theorem moves that test outside the independent proposal integral.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace SampLib.DiscreteLaplace

noncomputable section

def credit (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ z, F z ∂law s t hs ht

def factor (s t : ℕ) (ht : 0 < t) : ℝ≥0 :=
  AcceptedProposal.factor (proposal t ht) (acceptance s t ht)

theorem one_lt_factor (s t : ℕ) (ht : 0 < t) : 1 < factor s t ht :=
  AcceptedProposal.one_lt_factor _ _ (mass_nonzero s t ht)

theorem whole_lt_one : (wholeBias : ℝ) < 1 := by
  simp [wholeBias, ExpMinusRational.bias]

def retryCredit (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  credit s t hs ht F + factor s t ht * ε

def signCredit (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞)
    (r w : ℕ) (b : Bool) : ℝ≥0∞ :=
  if b = false ∧ magnitude s t (r, (w, b)) = 0 then retryCredit s t hs ht F ε
  else F (output s t (r, (w, b)))

def wholeCredit (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞)
    (r w : ℕ) : ℝ≥0∞ :=
  ∫⁻ b, signCredit s t hs ht F ε r w b ∂RealCoin.law VonNeumann.fairBias

def expCredit (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞)
    (r : ℕ) (accepted : Bool) : ℝ≥0∞ :=
  if accepted then ∫⁻ w, wholeCredit s t hs ht F ε r w ∂GeometricFailures.law wholeBias
  else retryCredit s t hs ht F ε

def rankCredit (s t : ℕ) (hs : 0 < s) (ht : 0 < t) (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞)
    (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ accepted, expCredit s t hs ht F ε r accepted
    ∂RealCoin.law (ExpMinusRational.bias r t (by positivity) (by exact_mod_cast ht))

private theorem kernel_coin (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (z : Sample) :
    AcceptedProposal.kernel (proposal t ht) (acceptance s t ht) (mass_nonzero s t ht)
      (fun z => F (output s t z)) ε z =
      ∫⁻ accepted, (if accepted then signCredit s t hs ht F ε z.1 z.2.1 z.2.2
        else retryCredit s t hs ht F ε)
        ∂RealCoin.law (ExpMinusRational.bias z.1 t (by positivity) (by exact_mod_cast ht)) := by
  rcases z with ⟨r, w, b⟩
  rw [AcceptedProposal.kernel, AcceptedProposal.credit, expectation s t hs ht F,
    RealCoin.lintegral_law]
  by_cases hbad : b = false ∧ magnitude s t (r, (w, b)) = 0
  · rcases hbad with ⟨rfl, hzero⟩
    simp only [RealCoin.credit, Bool.false_eq_true, ite_true, ite_false, signCredit,
      hzero, and_true, acceptance, AcceptedProposal.weight, AcceptedProposal.rejectedWeight,
      Set.Icc.coe_zero, ENNReal.ofReal_zero, sub_zero, ENNReal.ofReal_one,
      zero_mul, one_mul, zero_add]
    rw [← add_mul, RealCoin.pmf_sum, one_mul]
    rfl
  · simp [RealCoin.credit, RealCoin.pmf, signCredit, hbad, acceptance,
      AcceptedProposal.weight, AcceptedProposal.rejectedWeight, retryCredit, credit, factor]

private theorem row_expectation (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) (r : ℕ) :
    ∫⁻ z, AcceptedProposal.kernel (proposal t ht) (acceptance s t ht) (mass_nonzero s t ht)
      (fun z => F (output s t z)) ε (r, z)
      ∂((GeometricFailures.law wholeBias).prod (RealCoin.law VonNeumann.fairBias)) =
      rankCredit s t hs ht F ε r := by
  simp_rw [kernel_coin s t hs ht F ε]
  rw [lintegral_lintegral_swap
    (μ := (GeometricFailures.law wholeBias).prod (RealCoin.law VonNeumann.fairBias))
    (ν := RealCoin.law (ExpMinusRational.bias r t (by positivity) (by exact_mod_cast ht)))
    (f := fun (z : ℕ × Bool) (a : Bool) =>
      if a then signCredit s t hs ht F ε r z.1 z.2 else retryCredit s t hs ht F ε)
    (measurable_of_countable _).aemeasurable]
  unfold rankCredit
  apply lintegral_congr_ae
  apply Filter.Eventually.of_forall
  intro accepted
  cases accepted with
  | false => simp [expCredit]
  | true =>
    simp only [expCredit, ite_true, wholeCredit]
    exact lintegral_prod _ (measurable_of_countable _).aemeasurable

/-- The two retry branches share the accepted-proposal amplification factor. -/
theorem expectation_preservation (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ r ∈ Finset.range t, rankCredit s t hs ht F ε r) / t ≤ credit s t hs ht F + ε := by
  let : NeZero t := ⟨ht.ne'⟩
  have h := AcceptedProposal.expectation_preservation (proposal t ht) (acceptance s t ht)
    (measurable_of_countable _) (mass_nonzero s t ht)
    (fun z => F (output s t z)) (measurable_of_countable _) ε
  rw [AcceptedProposal.credit, expectation s t hs ht F] at h
  have hrows : (∫⁻ z, AcceptedProposal.kernel (proposal t ht) (acceptance s t ht)
      (mass_nonzero s t ht) (fun z => F (output s t z)) ε z ∂proposal t ht) =
      (∑ r ∈ Finset.range t, rankCredit s t hs ht F ε r) / t := by
    change (∫⁻ z, AcceptedProposal.kernel (proposal t ht) (acceptance s t ht)
      (mass_nonzero s t ht) (fun z => F (output s t z)) ε z
      ∂(UniformInt.law t).prod ((GeometricFailures.law wholeBias).prod
        (RealCoin.law VonNeumann.fairBias))) = _
    rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
    simp_rw [row_expectation s t hs ht F ε]
    exact UniformInt.lintegral_law t _
  simpa only [hrows, credit] using h

end

end SampLib.DiscreteLaplace
