module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Algebra.Order.Interval.Set.Group

@[expose] public section

/-! # Dyadic posterior laws for cached uniform bits

A cached prefix describes a uniform point in one dyadic cell. Reading a fresh bit
splits that posterior into its two equal-mass children. All credit identities use
ENNReal integrals and therefore allow unbounded or infinite continuations.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SampLib.DyadicPosterior

noncomputable section

/-- Unit uniform with a half-open support, fixing the binary endpoint convention. -/
def unitLaw : Measure ℝ := volume.restrict (Ico 0 1)

instance : IsProbabilityMeasure unitLaw where
  measure_univ := by simp [unitLaw]

/-- Prepending one binary digit to a fractional tail. -/
def half (b : Bool) (u : ℝ) : ℝ := ((if b then 1 else 0 : ℝ) + u) / 2

theorem measurable_half (b : Bool) : Measurable (half b) := by
  unfold half
  fun_prop

/-- A prefix acts as an increasing affine map of the remaining unit interval. -/
def embed : List Bool → ℝ → ℝ
  | [], u => u
  | b :: p, u => half b (embed p u)

theorem measurable_embed (p : List Bool) : Measurable (embed p) := by
  induction p with
  | nil => exact measurable_id
  | cons b p IH => exact (measurable_half b).comp IH

/-- Uniform posterior determined by a finite cached prefix. -/
def law (p : List Bool) : Measure ℝ := unitLaw.map (embed p)

instance (p : List Bool) : IsProbabilityMeasure (law p) where
  measure_univ := by
    rw [law, Measure.map_apply (measurable_embed p) MeasurableSet.univ]
    simp

@[simp] theorem law_nil : law [] = unitLaw := by simp [law, embed]

theorem law_cons (b : Bool) (p : List Bool) : law (b :: p) = (law p).map (half b) := by
  simpa only [law, embed, Function.comp_def] using
    (Measure.map_map (μ := unitLaw) (measurable_half b) (measurable_embed p)).symm

theorem embed_append (p q : List Bool) (u : ℝ) : embed (p ++ q) u = embed p (embed q u) := by
  induction p with
  | nil => rfl
  | cons b p IH => simp only [List.cons_append, embed, IH]

theorem law_append (p q : List Bool) : law (p ++ q) = (law q).map (embed p) := by
  rw [law, law, Measure.map_map (measurable_embed p) (measurable_embed q)]
  congr 1
  funext u
  exact embed_append p q u

/-- Expected credit conditional on the cached prefix. -/
def credit (p : List Bool) (F : ℝ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ u, F u ∂law p

/-- A known head bit deterministically changes coordinates to the tail posterior. -/
theorem credit_cons (b : Bool) (p : List Bool) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    credit (b :: p) F = credit p (fun u => F (half b u)) := by
  unfold credit
  rw [law_cons, lintegral_map hF (measurable_half b)]

theorem credit_append (p q : List Bool) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    credit (p ++ q) F = credit q (fun u => F (embed p u)) := by
  unfold credit
  rw [law_append, lintegral_map hF (measurable_embed p)]

/-- Affine images of a unit uniform are normalized uniforms on the image interval. -/
theorem map_unit_affine (a w : ℝ) (hw : 0 < w) :
    unitLaw.map (fun u => a + w * u) =
      ENNReal.ofReal w⁻¹ • volume.restrict (Ico a (a + w)) := by
  have hf : Measurable (fun u : ℝ => a + w * u) := by fun_prop
  have hshift : Measurable (fun u : ℝ => a + u) := by fun_prop
  have hscale : Measurable (fun u : ℝ => w * u) := by fun_prop
  have hpre : (fun u : ℝ => a + w * u) ⁻¹' Ico a (a + w) = Ico 0 1 := by
    ext u
    simp only [mem_preimage, mem_Ico]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> nlinarith
  have hmap : volume.map (fun u : ℝ => a + w * u) = ENNReal.ofReal w⁻¹ • volume := by
    calc
      _ = (volume.map (fun u : ℝ => w * u)).map (fun u : ℝ => a + u) := by
        rw [Measure.map_map hshift hscale]
        rfl
      _ = _ := by
        rw [Real.map_volume_mul_left hw.ne', Measure.map_smul _ hshift.aemeasurable,
          map_add_left_eq_self]
        simp only [abs_of_pos (inv_pos.mpr hw)]
  rw [unitLaw, ← hpre, ← Measure.restrict_map hf measurableSet_Ico, hmap,
    Measure.restrict_smul]

/-- Width of the cell left after a finite prefix. -/
def width (p : List Bool) : ℝ := (2 ^ p.length : ℝ)⁻¹

theorem width_pos (p : List Bool) : 0 < width p := by
  exact inv_pos.mpr (pow_pos (by norm_num) _)

theorem embed_affine (p : List Bool) (u : ℝ) :
    embed p u = embed p 0 + width p * u := by
  induction p with
  | nil => simp [embed, width]
  | cons b p IH =>
    simp only [embed, IH, width, List.length_cons, pow_succ, mul_inv_rev, half]
    ring

/-- The half-open dyadic cell described by the cached digits. -/
def cell (p : List Bool) : Set ℝ := Ico (embed p 0) (embed p 0 + width p)

/-- The posterior is precisely normalized Lebesgue measure on its dyadic cell. -/
theorem law_eq_uniform (p : List Bool) :
    law p = ENNReal.ofReal (width p)⁻¹ • volume.restrict (cell p) := by
  unfold law cell
  have he : embed p = fun u => embed p 0 + width p * u := funext (embed_affine p)
  rw [he]
  simpa only [mul_zero, add_zero] using map_unit_affine (embed p 0) _ (width_pos p)

instance (p : List Bool) : NullSingletonClass (law p) where
  measure_singleton u := by
    rw [law_eq_uniform, Measure.smul_apply]
    simp

theorem ae_mem_cell (p : List Bool) : ∀ᵐ u ∂law p, u ∈ cell p := by
  rw [law_eq_uniform]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ico) _

theorem embed_mem_unit (p : List Bool) {u : ℝ} (hu : u ∈ Ico 0 1) :
    embed p u ∈ Ico 0 1 := by
  induction p with
  | nil => exact hu
  | cons b p IH =>
    change 0 ≤ half b (embed p u) ∧ half b (embed p u) < 1
    cases b <;> simp only [half, Bool.false_eq_true, ite_false, ite_true] <;>
      constructor <;> linarith [IH.1, IH.2]

theorem ae_mem_unit (p : List Bool) : ∀ᵐ u ∂law p, u ∈ Ico 0 1 := by
  unfold law
  apply (ae_map_iff (measurable_embed p).aemeasurable
    (show MeasurableSet {u : ℝ | u ∈ Ico 0 1} from measurableSet_Ico)).mpr
  exact (ae_restrict_mem measurableSet_Ico).mono fun u hu => embed_mem_unit p hu

/-- Comparison is decided throughout the remaining posterior, up to null endpoints. -/
def resolves (p : List Bool) (t : ℝ) (b : Bool) : Prop :=
  ∀ᵐ u ∂law p, decide (u < t) = b

theorem resolves_false (p : List Bool) {t : ℝ} (ht : t ≤ 0) : resolves p t false := by
  exact (ae_mem_unit p).mono fun u hu => by simp [not_lt.mpr (ht.trans hu.1)]

theorem resolves_true (p : List Bool) {t : ℝ} (ht : 1 ≤ t) : resolves p t true := by
  exact (ae_mem_unit p).mono fun u hu => by simp [hu.2.trans_le ht]

/-- A cached head changes only the comparison's affine coordinate. -/
theorem resolves_cons (p : List Bool) (head result : Bool) (t : ℝ) :
    resolves (head :: p) t result ↔
      resolves p (2 * t - if head then 1 else 0) result := by
  unfold resolves
  have hm : MeasurableSet {u : ℝ | decide (u < t) = result} := by
    cases result
    · convert (measurableSet_Ici : MeasurableSet (Ici t)) using 1
      ext u
      simp
    · convert (measurableSet_Iio : MeasurableSet (Iio t)) using 1
      ext u
      simp
  rw [law_cons, ae_map_iff (measurable_half head).aemeasurable hm]
  have h (u : ℝ) : half head u < t ↔ u < 2 * t - if head then 1 else 0 := by
    unfold half
    constructor <;> intro h <;> linarith
  simp only [h]

/-- The two binary children partition the unit interval, each with mass one half. -/
theorem unit_split :
    unitLaw = (2 : ℝ≥0∞)⁻¹ • unitLaw.map (half false) +
      (2 : ℝ≥0∞)⁻¹ • unitLaw.map (half true) := by
  have hf : half false = (fun u : ℝ => 0 + (1 / 2) * u) := by
    funext u
    simp only [half, Bool.false_eq_true, ite_false]
    ring
  have ht : half true = (fun u : ℝ => (1 / 2) + (1 / 2) * u) := by
    funext u
    simp only [half, ite_true]
    ring
  have hfalse : unitLaw.map (half false) =
      (2 : ℝ≥0∞) • volume.restrict (Ico (0 : ℝ) (1 / 2)) := by
    rw [hf, map_unit_affine 0 (1 / 2) (by norm_num)]
    norm_num
  have htrue : unitLaw.map (half true) =
      (2 : ℝ≥0∞) • volume.restrict (Ico (1 / 2 : ℝ) 1) := by
    rw [ht, map_unit_affine (1 / 2) (1 / 2) (by norm_num)]
    norm_num
  rw [hfalse, htrue, smul_smul, smul_smul]
  simp only [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_smul]
  have hd : Disjoint (Ico (0 : ℝ) (1 / 2)) (Ico (1 / 2 : ℝ) 1) :=
    disjoint_left.mpr fun _ hx hy => not_lt_of_ge hy.1 hx.2
  rw [← Measure.restrict_union hd measurableSet_Ico,
    Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]
  rfl

/-- The posterior expectation is the average of its two refined children. -/
theorem credit_split (p : List Bool) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    credit p F = (credit (p ++ [false]) F + credit (p ++ [true]) F) / 2 := by
  have h := congrArg (fun μ : Measure ℝ => ∫⁻ u, F (embed p u) ∂μ) unit_split
  simp only [lintegral_add_measure, lintegral_smul_measure, smul_eq_mul] at h
  have hp := credit_append p [] F hF
  simp only [List.append_nil] at hp
  rw [hp, credit_append p [false] F hF, credit_append p [true] F hF]
  simpa only [credit, law_cons, law_nil,
    ENNReal.div_eq_inv_mul, mul_add] using h

end

end SampLib.DyadicPosterior
