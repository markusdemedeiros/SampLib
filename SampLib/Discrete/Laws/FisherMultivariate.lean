import SampLib.Discrete.Laws.FisherProposal

/-! # Multivariate Fisher noncentral hypergeometric sampling

Conditioning the independent binomial proposal on its total cancels the common
denominator, leaving masses proportional to `∏ᵢ choose(cᵢ,xᵢ) oᵢ^xᵢ`. Positive
odds make every feasible allocation possible.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.FisherMultivariate

noncomputable section

/-- A greedy allocation supplies a feasible count vector for every valid total. -/
def allocation (draws : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs => min draws c :: allocation (draws - min draws c) cs

theorem allocation_feasible (draws : ℕ) (counts : List ℕ) (hd : draws ≤ counts.sum) :
    List.Forall₂ (· ≤ ·) (allocation draws counts) counts ∧
      (allocation draws counts).sum = draws := by
  induction counts generalizing draws with
  | nil => simp only [List.sum_nil, Nat.le_zero] at hd; subst draws; simp [allocation]
  | cons c cs IH =>
    have hrest : draws - min draws c ≤ cs.sum := by
      simp only [List.sum_cons] at hd
      by_cases h : draws ≤ c
      · simp [min_eq_left h]
      · rw [min_eq_right (le_of_not_ge h)]
        omega
    have hr := IH (draws - min draws c) hrest
    exact ⟨List.Forall₂.cons (Nat.min_le_right _ _) hr.1,
      by simpa only [allocation, List.sum_cons, hr.2] using
        Nat.add_sub_of_le (Nat.min_le_left draws c)⟩

private theorem coefficient_pos (counts odds xs : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hxs : List.Forall₂ (· ≤ ·) xs counts) : 0 < coefficient counts odds xs := by
  induction counts generalizing odds xs with
  | nil =>
    have ho : odds = [] := List.length_eq_zero_iff.mp hlen.symm
    have hx : xs = [] := List.forall₂_nil_right_iff.mp hxs
    simp [ho, hx, coefficient]
  | cons c cs IH =>
    cases odds with
    | nil => simp at hlen
    | cons o os =>
      cases xs with
      | nil => simp at hxs
      | cons x xs =>
        have ht : cs.length = os.length := by simpa using hlen
        have ho : 0 < o := hodds o (by simp)
        have hos : ∀ j ∈ os, 0 < j := fun j hj => hodds j (by simp [hj])
        obtain ⟨hx, htail⟩ := List.forall₂_cons.mp hxs
        exact Nat.mul_pos (Nat.mul_pos (Nat.choose_pos hx) (Nat.pow_pos ho))
          (IH os xs ht hos htail)

theorem proposal_atom_pos (counts odds xs : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hxs : List.Forall₂ (· ≤ ·) xs counts) : 0 < (proposal counts odds) {xs} := by
  rw [proposal_singleton counts odds xs hlen]
  exact ENNReal.ofReal_pos.mpr (div_pos
    (by exact_mod_cast coefficient_pos counts odds xs hlen hodds hxs)
    (by exact_mod_cast denominator_pos counts odds))

/-- Accept precisely the requested total count. -/
def acceptance (draws : ℕ) (xs : List ℕ) : unitInterval := if xs.sum = draws then 1 else 0

@[simp] theorem acceptance_coe (draws : ℕ) (xs : List ℕ) :
    (acceptance draws xs : ℝ) = if xs.sum = draws then 1 else 0 := by
  by_cases h : xs.sum = draws <;> simp [acceptance, h]

theorem measurable_acceptance (draws : ℕ) : Measurable (acceptance draws) :=
  measurable_of_countable _

theorem weight_eq_indicator (draws : ℕ) :
    AcceptedProposal.weight (acceptance draws) = {xs : List ℕ | xs.sum = draws}.indicator 1 := by
  funext xs
  by_cases h : xs.sum = draws <;> simp [AcceptedProposal.weight, h]

theorem mass_eq (draws : ℕ) (counts odds : List ℕ) :
    AcceptedProposal.mass (proposal counts odds) (acceptance draws) =
      (proposal counts odds) {xs | xs.sum = draws} := by
  rw [AcceptedProposal.mass, weight_eq_indicator,
    lintegral_indicator_one (Set.to_countable _).measurableSet]

/-- Positive odds assign positive proposal mass to every feasible requested total. -/
theorem mass_nonzero (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) :
    AcceptedProposal.mass (proposal counts odds) (acceptance draws) ≠ 0 := by
  have hf := allocation_feasible draws counts hdraws
  have hp := proposal_atom_pos counts odds (allocation draws counts) hlen hodds hf.1
  have hs : {allocation draws counts} ⊆ {xs : List ℕ | xs.sum = draws} := by
    intro xs hx
    change xs.sum = draws
    simpa only [Set.mem_singleton_iff.mp hx] using hf.2
  rw [mass_eq]
  exact (hp.trans_le (measure_mono hs)).ne'

/-- The canonical Fisher law: independent odds-matched binomials conditioned on their sum. -/
def law (draws : ℕ) (counts odds : List ℕ) (hlen : counts.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) (hdraws : draws ≤ counts.sum) : Measure (List ℕ) :=
  AcceptedProposal.law (proposal counts odds) (acceptance draws)
    (mass_nonzero draws counts odds hlen hodds hdraws)

instance (draws : ℕ) (counts odds : List ℕ) (hlen : counts.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) (hdraws : draws ≤ counts.sum) :
    IsProbabilityMeasure (law draws counts odds hlen hodds hdraws) := by
  dsimp [law]
  infer_instance

/-- Conditioning is normalized restriction to the requested total. -/
theorem law_eq_restrict (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) :
    law draws counts odds hlen hodds hdraws =
      (AcceptedProposal.mass (proposal counts odds) (acceptance draws))⁻¹ •
        (proposal counts odds).restrict {xs | xs.sum = draws} := by
  rw [law, AcceptedProposal.law, weight_eq_indicator,
    withDensity_indicator_one (Set.to_countable _).measurableSet]

/-- Every accepted vector has the requested sum and the original population bounds. -/
theorem law_support (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) :
    ∀ᵐ xs ∂law draws counts odds hlen hodds hdraws,
      xs.length = counts.length ∧ List.Forall₂ (· ≤ ·) xs counts ∧ xs.sum = draws := by
  rw [law_eq_restrict]
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae (proposal_support counts odds hlen),
    ae_restrict_mem (Set.to_countable _).measurableSet] with xs hs hx
  exact ⟨hs.1, hs.2, hx⟩

/-- The finite positive normalizing constant in the standard Fisher point masses. -/
def normalizer (draws : ℕ) (counts odds : List ℕ) : ℝ :=
  (AcceptedProposal.mass (proposal counts odds) (acceptance draws)).toReal *
    denominator counts odds

theorem normalizer_pos (draws : ℕ) (counts odds : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) : 0 < normalizer draws counts odds :=
  mul_pos (ENNReal.toReal_pos (mass_nonzero draws counts odds hlen hodds hdraws)
    (AcceptedProposal.mass_ne_top _ _)) (by exact_mod_cast denominator_pos counts odds)

/-- The canonical Fisher mass is proportional to the product of binomial coefficients
and integer odds powers, restricted to the requested total. -/
theorem law_singleton (draws : ℕ) (counts odds xs : List ℕ)
    (hlen : counts.length = odds.length) (hodds : ∀ o ∈ odds, 0 < o)
    (hdraws : draws ≤ counts.sum) :
    (law draws counts odds hlen hodds hdraws) {xs} =
      if xs.sum = draws then
        ENNReal.ofReal ((coefficient counts odds xs : ℝ) / normalizer draws counts odds)
      else 0 := by
  let m := AcceptedProposal.mass (proposal counts odds) (acceptance draws)
  have hm0 : m ≠ 0 := mass_nonzero draws counts odds hlen hodds hdraws
  have hmf : m ≠ ∞ := AcceptedProposal.mass_ne_top _ _
  have hmp : 0 < m.toReal := ENNReal.toReal_pos hm0 hmf
  have hinv : m⁻¹ = ENNReal.ofReal (m.toReal)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hmp, ENNReal.ofReal_toReal hmf]
  rw [law, AcceptedProposal.law, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton _), lintegral_singleton]
  by_cases h : xs.sum = draws
  · simp only [AcceptedProposal.weight, acceptance_coe, h, ite_true,
      ENNReal.ofReal_one, one_mul]
    rw [proposal_singleton counts odds xs hlen, hinv,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hmp.le)]
    congr 1
    simp only [normalizer, m, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp [AcceptedProposal.weight, h]

private theorem eq_dirac_of_ae (μ : Measure (List ℕ)) [IsProbabilityMeasure μ]
    (target : List ℕ) (h : ∀ᵐ xs ∂μ, xs = target) : μ = Measure.dirac target := by
  apply Measure.ext_of_lintegral
  intro F _
  rw [lintegral_dirac]
  calc
    _ = ∫⁻ _ : List ℕ, F target ∂μ := lintegral_congr_ae (h.mono fun xs hx => congrArg F hx)
    _ = F target := by simp

private theorem eq_of_bounds_sum {xs counts : List ℕ}
    (h : List.Forall₂ (· ≤ ·) xs counts) (hs : xs.sum = counts.sum) : xs = counts := by
  revert hs
  induction h with
  | nil => intro; rfl
  | @cons x c xs cs hx ht IH =>
    intro hs
    have htail := List.Forall₂.sum_le_sum ht
    simp only [List.sum_cons] at hs
    have he : x = c := by omega
    subst c
    congr 1
    exact IH (by omega)

/-- Drawing zero items returns the zero vector, including the empty population. -/
theorem law_zero (counts odds : List ℕ) (hlen : counts.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) :
    law 0 counts odds hlen hodds (Nat.zero_le _) =
      Measure.dirac (List.replicate counts.length 0) := by
  apply eq_dirac_of_ae
  filter_upwards [law_support 0 counts odds hlen hodds (Nat.zero_le _)] with xs hs
  have hx : xs = List.replicate xs.length 0 :=
    List.eq_replicate_length.mpr (List.sum_eq_zero_iff.mp hs.2.2)
  simpa only [hs.1] using hx

/-- Drawing the entire population returns its original count vector. -/
theorem law_full (counts odds : List ℕ) (hlen : counts.length = odds.length)
    (hodds : ∀ o ∈ odds, 0 < o) :
    law counts.sum counts odds hlen hodds le_rfl = Measure.dirac counts := by
  apply eq_dirac_of_ae
  filter_upwards [law_support counts.sum counts odds hlen hodds le_rfl] with xs hs
  exact eq_of_bounds_sum hs.2.1 hs.2.2

end

end SampLib.FisherMultivariate
