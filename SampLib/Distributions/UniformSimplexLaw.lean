module

public import SampLib.Distributions.PSRNDirichletLaw
public import SampLib.Distributions.JohnkBeta
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-! # Normalized exponentials are uniform on the simplex

The uniform law on the standard simplex in `ℝ^(m+1)` is `m!` times Lebesgue measure on the
open region `{y ∈ ℝ^m | y > 0, ∑ y < 1}`, embedded by appending `1 - ∑ y`.

Normalizing `m + 1` independent unit exponentials gives exactly this law. By induction on
`m`, the exponential vector factors into its sum, with law `Gamma(m+1)`, and an independent
uniform simplex point. Adding one more exponential uses the beta–gamma split of the old sum
and the new coordinate. A `Beta(m+1, 1)` scaling of an `m`-simplex point then fills the
`(m+1)`-simplex: scaling contributes the Jacobian `u^m`, and a translation identifies the
new coordinate.
-/

open Set MeasureTheory ProbabilityTheory Real
open ENNReal (ofReal)
open scoped ENNReal Nat

namespace SampLib.UniformSimplex

noncomputable section

/-- The open standard simplex, recorded by its first `m` coordinates. -/
def region (m : ℕ) : Set (Fin m → ℝ) := {y | (∀ i, 0 < y i) ∧ ∑ i, y i < 1}

/-- The canonical uniform law: density `m!` on the open simplex region. -/
def law (m : ℕ) : Measure (Fin m → ℝ) := ((m ! : ℕ) : ℝ≥0∞) • volume.restrict (region m)

/-- Complete a region point with its last barycentric coordinate. -/
def embed {m : ℕ} (y : Fin m → ℝ) : Fin (m + 1) → ℝ := Fin.snoc y (1 - ∑ i, y i)

theorem measurable_snoc (m : ℕ) :
    Measurable (fun p : (Fin m → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (m + 1) → ℝ)) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm.measurable
  convert h.comp (measurable_snd.prodMk measurable_fst) using 1
  funext p
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']

/-- The region scaled by `u`. -/
def scaled (m : ℕ) (u : ℝ) : Set (Fin m → ℝ) := {w | (∀ i, 0 < w i) ∧ ∑ i, w i < u}

theorem measurableSet_scaled (m : ℕ) (u : ℝ) : MeasurableSet (scaled m u) := by
  have hpos : MeasurableSet {y : Fin m → ℝ | ∀ i, 0 < y i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  exact hpos.inter (measurableSet_lt
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const)

theorem measurableSet_region (m : ℕ) : MeasurableSet (region m) := measurableSet_scaled m 1

theorem mem_scaled_smul {m : ℕ} {u : ℝ} (hu : 0 < u) (y : Fin m → ℝ) :
    u • y ∈ scaled m u ↔ y ∈ region m := by
  simp only [scaled, region, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
    mul_pos_iff_of_pos_left hu, mul_lt_iff_lt_one_right hu]

/-- Scaling by `u > 0` carries the region onto `scaled m u`, with Jacobian `u ^ m`. -/
theorem lintegral_scale (m : ℕ) {u : ℝ} (hu : 0 < u) (g : (Fin m → ℝ) → ℝ≥0∞)
    (hg : Measurable g) :
    ofReal (u ^ m) * ∫⁻ y, (region m).indicator (fun y => g (u • y)) y =
      ∫⁻ w, (scaled m u).indicator g w := by
  have hind : (region m).indicator (fun y => g (u • y)) =
      fun y => (scaled m u).indicator g (u • y) := by
    funext y
    by_cases hy : y ∈ region m
    · rw [indicator_of_mem hy, indicator_of_mem ((mem_scaled_smul hu y).mpr hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (mt (mem_scaled_smul hu y).mp hy)]
  rw [hind, ← lintegral_map (hg.indicator (measurableSet_scaled m u)) (measurable_const_smul u),
    Measure.map_addHaar_smul volume hu.ne', lintegral_smul_measure, Module.finrank_fin_fun,
    smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

theorem measurable_embed (m : ℕ) : Measurable (embed (m := m)) :=
  (measurable_snoc m).comp (measurable_id.prodMk (by fun_prop))

instance (m : ℕ) : SFinite (law m) := by
  unfold law
  infer_instance

theorem lintegral_law (m : ℕ) (g : (Fin m → ℝ) → ℝ≥0∞) :
    ∫⁻ y, g y ∂law m = ((m ! : ℕ) : ℝ≥0∞) * ∫⁻ y, (region m).indicator g y := by
  rw [law, lintegral_smul_measure, lintegral_indicator (measurableSet_region m), smul_eq_mul]

/-- On the unit interval, `Beta(m+1, 1)` has density `(m+1) u^m`. -/
theorem betaPDF_succ_one (m : ℕ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDF (m + 1) 1 u = ((m + 1 : ℕ) : ℝ≥0∞) * ofReal (u ^ m) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  rw [betaPDF_eq, ite_eq_left (show 0 < u ∧ u < 1 from hu), JohnkBeta.beta_one _ hm,
    one_div_one_div, add_sub_cancel_right,
    sub_self, rpow_zero, mul_one, rpow_natCast, ENNReal.ofReal_mul hm.le]
  push_cast
  rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

theorem betaPDF_succ_one_of_notMem (m : ℕ) {u : ℝ} (hu : u ∉ Ioo (0 : ℝ) 1) :
    betaPDF (m + 1) 1 u = 0 := by
  rw [betaPDF_eq, ite_eq_right (show ¬(0 < u ∧ u < 1) from hu), ENNReal.ofReal_zero]

/-- A point of the open `(m+1)`-simplex, split into its first `m` coordinates and the next. -/
theorem snoc_mem_region {m : ℕ} (w : Fin m → ℝ) (v : ℝ) :
    (Fin.snoc w v : Fin (m + 1) → ℝ) ∈ region (m + 1) ↔
      (∀ i, 0 < w i) ∧ 0 < v ∧ ∑ i, w i + v < 1 := by
  simp only [region, mem_ofPred_eq, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
    Fin.sum_univ_castSucc, and_assoc]

/-- Lebesgue measure on `ℝ^(m+1)`, split into the first `m` coordinates and the last. -/
theorem lintegral_snoc (m : ℕ) (h : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z, h z = ∫⁻ w, ∫⁻ v, h (Fin.snoc w v) := by
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
  have hsnoc : Measurable (fun p : ℝ × (Fin m → ℝ) => h (Fin.snoc p.2 p.1)) :=
    hh.comp ((measurable_snoc m).comp (measurable_snd.prodMk measurable_fst))
  rw [← he.lintegral_comp hh]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk,
    Fin.insertNth_last']
  rw [Measure.volume_eq_prod, lintegral_prod _ hsnoc.aemeasurable]
  exact lintegral_lintegral_swap hsnoc.aemeasurable

/-- The pairs `(w, u)` with `0 < u < 1` and `w` in the `u`-scaled region. -/
def cone (m : ℕ) : Set ((Fin m → ℝ) × ℝ) := {p | p.2 ∈ Ioo (0 : ℝ) 1 ∧ p.1 ∈ scaled m p.2}

theorem measurableSet_cone (m : ℕ) : MeasurableSet (cone m) := by
  have hpos : MeasurableSet {p : (Fin m → ℝ) × ℝ | ∀ i, 0 < p.1 i} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)
  have hsum : MeasurableSet {p : (Fin m → ℝ) × ℝ | ∑ i, p.1 i < p.2} :=
    measurableSet_lt (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_fst) measurable_snd
  exact (measurable_snd measurableSet_Ioo).inter (hpos.inter hsum)

/-- Scaling an `m`-simplex point by an independent `Beta(m+1, 1)` fills the `(m+1)`-simplex. -/
theorem lintegral_beta_fill (m : ℕ) (f : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ u, betaPDF (m + 1) 1 u *
        ∫⁻ y, f (Fin.snoc (u • y) (u * (1 - ∑ i, y i))) ∂law m =
      ∫⁻ z, f z ∂law (m + 1) := by
  let T : (Fin m → ℝ) × ℝ → ℝ≥0∞ :=
    (cone m).indicator (fun p => f (Fin.snoc p.1 (p.2 - ∑ i, p.1 i)))
  have hT : Measurable T := (hf.comp ((measurable_snoc m).comp (measurable_fst.prodMk
    (measurable_snd.sub (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp measurable_fst))))).indicator (measurableSet_cone m)
  have hc : ((m + 1 : ℕ) ! : ℝ≥0∞) = ((m + 1 : ℕ) : ℝ≥0∞) * ((m ! : ℕ) : ℝ≥0∞) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  calc
    _ = ∫⁻ u, ((m + 1 : ℕ) ! : ℝ≥0∞) * ∫⁻ w, T (w, u) := by
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Ioo (0 : ℝ) 1
      · have hg : Measurable (fun w : Fin m → ℝ => f (Fin.snoc w (u - ∑ i, w i))) :=
          hf.comp ((measurable_snoc m).comp (measurable_id.prodMk
            (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i))))
        have hscale := lintegral_scale m hu.1 _ hg
        have hT_eq : (fun w => T (w, u)) =
            (scaled m u).indicator (fun w => f (Fin.snoc w (u - ∑ i, w i))) := by
          funext w
          by_cases hw : w ∈ scaled m u
          · rw [indicator_of_mem hw]
            exact indicator_of_mem (show (w, u) ∈ cone m from ⟨hu, hw⟩) _
          · rw [indicator_of_notMem hw]
            exact indicator_of_notMem (fun h => hw h.2) _
        have hy : (fun y : Fin m → ℝ => f (Fin.snoc (u • y) (u * (1 - ∑ i, y i)))) =
            fun y => f (Fin.snoc (u • y) (u - ∑ i, (u • y) i)) := by
          funext y
          simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_sub, mul_one]
        rw [betaPDF_succ_one m hu, lintegral_law, hy, hT_eq, ← hscale, hc]
        ring
      · rw [betaPDF_succ_one_of_notMem m hu, zero_mul]
        have hzero : (fun w => T (w, u)) = 0 := by
          funext w
          exact indicator_of_notMem (fun h => hu h.1) _
        rw [hzero, Pi.zero_def, lintegral_zero, mul_zero]
    _ = ((m + 1 : ℕ) ! : ℝ≥0∞) * ∫⁻ w, ∫⁻ u, T (w, u) := by
      rw [lintegral_const_mul _ hT.lintegral_prod_left']
      congr 1
      exact lintegral_lintegral_swap (hT.comp measurable_swap).aemeasurable
    _ = ((m + 1 : ℕ) ! : ℝ≥0∞) * ∫⁻ w, ∫⁻ v, (region (m + 1)).indicator f (Fin.snoc w v) := by
      congr 1
      apply lintegral_congr
      intro w
      rw [← lintegral_add_right_eq_self (fun u => T (w, u)) (∑ i, w i)]
      apply lintegral_congr
      intro v
      have hmem : (w, v + ∑ i, w i) ∈ cone m ↔
          (Fin.snoc w v : Fin (m + 1) → ℝ) ∈ region (m + 1) := by
        rw [snoc_mem_region]
        have hsum : (∀ i, 0 < w i) → 0 ≤ ∑ i, w i :=
          fun h => Finset.sum_nonneg fun i _ => (h i).le
        simp only [cone, scaled, mem_ofPred_eq, mem_Ioo]
        constructor
        · rintro ⟨⟨_, h1⟩, hw, h2⟩
          exact ⟨hw, by linarith, by linarith⟩
        · rintro ⟨hw, hv, h1⟩
          have := hsum hw
          exact ⟨⟨by linarith, by linarith⟩, hw, by linarith⟩
      by_cases h : (Fin.snoc w v : Fin (m + 1) → ℝ) ∈ region (m + 1)
      · rw [indicator_of_mem h]
        simp only [T, indicator_of_mem (hmem.mpr h), add_sub_cancel_right]
      · rw [indicator_of_notMem h]
        exact indicator_of_notMem (mt hmem.mp h) _
    _ = _ := by
      rw [lintegral_law, lintegral_snoc _ _ (hf.indicator (measurableSet_region _))]

theorem embed_snoc {m : ℕ} (y : Fin m → ℝ) (u : ℝ) :
    embed (Fin.snoc (u • y) (u * (1 - ∑ i, y i)) : Fin (m + 1) → ℝ) =
      Fin.snoc (u • embed y) (1 - u) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [embed, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Pi.smul_apply,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [embed]
    · simp [embed]

theorem smul_snoc {m : ℕ} (s : ℝ) (a : Fin m → ℝ) (b : ℝ) :
    s • (Fin.snoc a b : Fin (m + 1) → ℝ) = Fin.snoc (s • a) (s * b) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)

theorem gammaPDF_ne_top (a r x : ℝ) : gammaPDF a r x ≠ ∞ := ENNReal.ofReal_ne_top

theorem betaPDF_ne_top (a b x : ℝ) : betaPDF a b x ≠ ∞ := ENNReal.ofReal_ne_top

theorem lintegral_gammaMeasure (a r : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g t ∂gammaMeasure a r = ∫⁻ t, gammaPDF a r t * g t :=
  lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaPDF a r) hg

/-- Independent unit exponentials split into a `Gamma(m+1)` sum and an independent uniform
point of the simplex: `x = s • embed y`. -/
theorem lintegral_exponentials (m : ℕ) (G : (Fin (m + 1) → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂Measure.pi (fun _ : Fin (m + 1) => gammaMeasure 1 1) =
      ∫⁻ s, gammaPDF (m + 1) 1 s * ∫⁻ y, G (s • embed y) ∂law m := by
  have := isProbabilityMeasure_gammaMeasure (zero_lt_one' ℝ) (zero_lt_one' ℝ)
  induction m with
  | zero =>
    have he := (measurePreserving_funUnique (gammaMeasure 1 1) (Fin 1)).symm
    refine (he.lintegral_comp hG).symm.trans ?_
    rw [lintegral_gammaMeasure 1 1 (g := fun t => G ((MeasurableEquiv.funUnique (Fin 1) ℝ).symm t))
      (hG.comp he.measurable)]
    apply lintegral_congr
    intro s
    have hlaw : ∫⁻ y, G (s • embed y) ∂law 0 = G (fun _ => s) := by
      rw [lintegral_law, volume_pi, Measure.pi_of_empty, lintegral_dirac]
      have hmem : (isEmptyElim : Fin 0 → ℝ) ∈ region 0 := by simp [region]
      rw [indicator_of_mem hmem, Nat.factorial_zero, Nat.cast_one, one_mul]
      congr 1
      funext i
      obtain rfl : i = Fin.last 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      simp only [embed, Pi.smul_apply, smul_eq_mul, Fin.snoc_last, Finset.univ_eq_empty,
        Finset.sum_empty, sub_zero, mul_one]
    rw [hlaw, Nat.cast_zero, zero_add]
    rfl
  | succ m ih =>
    -- The new coordinate `t` beside the old sum `r` and simplex point `y`.
    let H : ℝ → ℝ → (Fin m → ℝ) → ℝ≥0∞ := fun r t y => G (Fin.snoc (r • embed y) t)
    have hH : Measurable (fun p : (ℝ × ℝ) × (Fin m → ℝ) => H p.1.1 p.1.2 p.2) :=
      hG.comp ((measurable_snoc (m + 1)).comp
        (((measurable_fst.comp measurable_fst).smul
          ((measurable_embed m).comp measurable_snd)).prodMk (measurable_snd.comp measurable_fst)))
    have hsnoc : Measurable (fun p : (Fin (m + 1) → ℝ) × ℝ => G (Fin.snoc p.1 p.2)) :=
      hG.comp (measurable_snoc (m + 1))
    have hJ : Measurable (fun p : (ℝ × (Fin m → ℝ)) × ℝ =>
        gammaPDF (m + 1) 1 p.1.1 * gammaPDF 1 1 p.2 * H p.1.1 p.2 p.1.2) :=
      (((measurable_gammaPDF _ 1).comp (measurable_fst.comp measurable_fst)).mul
        ((measurable_gammaPDF 1 1).comp measurable_snd)).mul
        (hH.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
          (measurable_snd.comp measurable_fst)))
    have hK : Measurable (fun p : ((Fin m → ℝ) × ℝ) × ℝ =>
        betaPDF (m + 1) 1 p.2 * gammaPDF (m + 1 + 1) 1 p.1.2 *
          H (p.1.2 * p.2) (p.1.2 * (1 - p.2)) p.1.1) :=
      (((measurable_betaPDFReal _ 1).ennreal_ofReal.comp measurable_snd).mul
        ((measurable_gammaPDF _ 1).comp (measurable_snd.comp measurable_fst))).mul
        (hH.comp ((((measurable_snd.comp measurable_fst).mul measurable_snd).prodMk
          ((measurable_snd.comp measurable_fst).mul (measurable_const.sub measurable_snd))).prodMk
          (measurable_fst.comp measurable_fst)))
    have he := (measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1 + 1) => gammaMeasure 1 1) (Fin.last (m + 1))).symm
    calc
      _ = ∫⁻ x, ∫⁻ t, G (Fin.snoc x t) ∂gammaMeasure 1 1
            ∂Measure.pi (fun _ : Fin (m + 1) => gammaMeasure 1 1) := by
        refine (he.lintegral_comp hG).symm.trans ?_
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_last']
        exact lintegral_prod_symm' _ (hsnoc.comp (measurable_snd.prodMk measurable_fst))
      _ = ∫⁻ r, gammaPDF (m + 1) 1 r * ∫⁻ y, ∫⁻ t, H r t y ∂gammaMeasure 1 1 ∂law m :=
        ih _ hsnoc.lintegral_prod_right'
      _ = ∫⁻ r, ∫⁻ y, (∫⁻ t, gammaPDF (m + 1) 1 r * gammaPDF 1 1 t * H r t y) ∂law m := by
        apply lintegral_congr
        intro r
        rw [← lintegral_const_mul' _ _ (gammaPDF_ne_top _ _ _)]
        apply lintegral_congr
        intro y
        have ht : Measurable (fun t => H r t y) :=
          hH.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)
        rw [lintegral_gammaMeasure 1 1 ht, ← lintegral_const_mul' _ _ (gammaPDF_ne_top _ _ _)]
        apply lintegral_congr
        intro t
        ring
      _ = ∫⁻ y, (∫⁻ r, ∫⁻ t, gammaPDF (m + 1) 1 r * gammaPDF 1 1 t * H r t y) ∂law m :=
        lintegral_lintegral_swap hJ.lintegral_prod_right'.aemeasurable
      _ = ∫⁻ y, (∫⁻ s, ∫⁻ u, betaPDF (m + 1) 1 u * gammaPDF (m + 1 + 1) 1 s *
            H (s * u) (s * (1 - u)) y) ∂law m := by
        apply lintegral_congr
        intro y
        exact BetaExponentialProduct.gamma_pair_transform (m + 1) 1 1 (by positivity) one_pos
          one_pos (fun p => H p.1 p.2 y)
          (hH.comp (measurable_id.prodMk measurable_const))
      _ = ∫⁻ s, gammaPDF (m + 1 + 1) 1 s * ∫⁻ u, betaPDF (m + 1) 1 u *
            ∫⁻ y, H (s * u) (s * (1 - u)) y ∂law m := by
        rw [lintegral_lintegral_swap hK.lintegral_prod_right'.aemeasurable]
        apply lintegral_congr
        intro s
        have hyu : Measurable (Function.uncurry fun (y : Fin m → ℝ) (u : ℝ) =>
            betaPDF (m + 1) 1 u * gammaPDF (m + 1 + 1) 1 s * H (s * u) (s * (1 - u)) y) :=
          hK.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
        rw [lintegral_lintegral_swap hyu.aemeasurable, ← lintegral_const_mul' _ _
          (gammaPDF_ne_top _ _ _)]
        apply lintegral_congr
        intro u
        rw [← lintegral_const_mul' _ _ (betaPDF_ne_top _ _ _),
          ← lintegral_const_mul' _ _ (gammaPDF_ne_top _ _ _)]
        apply lintegral_congr
        intro y
        ring
      _ = _ := by
        push_cast
        apply lintegral_congr
        intro s
        rw [← lintegral_beta_fill m (fun z => G (s • embed z))
          (hG.comp ((measurable_embed _).const_smul s))]
        congr 1
        apply lintegral_congr
        intro u
        congr 1
        apply lintegral_congr
        intro y
        simp only [H, embed_snoc, smul_snoc, smul_smul]

theorem total_embed {m : ℕ} (y : Fin m → ℝ) : PSRNDirichletLaw.total (embed y) = 1 := by
  simp [PSRNDirichletLaw.total, embed, Fin.sum_univ_castSucc]

theorem normalize_smul_embed {m : ℕ} {s : ℝ} (hs : s ≠ 0) (y : Fin m → ℝ) :
    PSRNDirichletLaw.normalize (s • embed y) = embed y := by
  funext i
  simp only [PSRNDirichletLaw.normalize, PSRNDirichletLaw.total, Pi.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  rw [show ∑ j, embed y j = 1 from total_embed y, mul_one, mul_div_cancel_left₀ _ hs]

/-- Normalized unit exponentials are uniform on the simplex: `m!` times Lebesgue measure on
`{y > 0, ∑ y < 1}`, completed by the last coordinate `1 - ∑ y`. -/
theorem simplex_eq (m : ℕ) : PSRNDirichletLaw.simplex (m + 1) = (law m).map embed := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map hF (measurable_embed m), PSRNDirichletLaw.simplex,
    PSRNDirichletLaw.expectation_preservation _ _ F hF, PSRNDirichletLaw.proposal,
    lintegral_exponentials m (fun x => F (PSRNDirichletLaw.normalize x))
      (hF.comp PSRNDirichletLaw.measurable_normalize)]
  calc
    _ = ∫⁻ s, gammaPDF (m + 1) 1 s * ∫⁻ y, F (embed y) ∂law m := by
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : ℝ)] with s hs
      simp only [normalize_smul_embed hs]
    _ = _ := by
      rw [lintegral_mul_const _ (measurable_gammaPDF _ 1),
        lintegral_gammaPDF_eq_one (by positivity) one_pos, one_mul]

/-- Equivalently, the first `m` coordinates have density `m!` on `{y > 0, ∑ y < 1}`. -/
theorem simplex_firstCoordinates (m : ℕ) :
    (PSRNDirichletLaw.simplex (m + 1)).map (fun x i => x (Fin.castSucc i)) = law m := by
  rw [simplex_eq, Measure.map_map (measurable_pi_iff.2 fun i => measurable_pi_apply _)
    (measurable_embed m)]
  convert Measure.map_id
  funext y i
  simp [embed]

end

end SampLib.UniformSimplex
