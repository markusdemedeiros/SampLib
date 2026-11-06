import SampLib.Latent.UniformBagPrefix
import SampLib.Common.Laws.DyadicRefinement

/-! # Exact intervals observed from a cached uniform

A read reveals a dyadic interval containing the same latent value. Its posterior
may depend on all earlier reads; only the returned interval's width depends on
the requested precision.
-/

open Set MeasureTheory

namespace SampLib.LatentUniform

noncomputable section

/-- The affine coordinate of a binary prefix is its integer rank in a dyadic grid. -/
theorem embed_eq_rank (p : List Bool) (u : ℝ) :
    DyadicPosterior.embed p u =
      ((UniformBag.rank p : ℝ) + u) / 2 ^ p.length := by
  induction p with
  | nil => simp [DyadicPosterior.embed, UniformBag.rank]
  | cons b p IH =>
    simp only [DyadicPosterior.embed, DyadicPosterior.half, UniformBag.rank,
      List.length_cons, IH, Int.cast_add, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat, pow_succ]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, Int.cast_zero,
      Int.cast_one]
    all_goals field_simp; ring

/-- The posterior's support is exactly the cell identified by the cached digits. -/
theorem cell_eq_rank (p : List Bool) :
    DyadicPosterior.cell p =
      Ico ((UniformBag.rank p : ℝ) / 2 ^ p.length)
        (((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length) := by
  simp only [DyadicPosterior.cell, embed_eq_rank, add_zero, DyadicPosterior.width]
  congr 1
  field_simp

/-- Reading at precision `n` exposes the original uniform's `n`-bit cell. -/
theorem ae_read_interval {p q : List Bool} {n : ℕ}
    (hread : UniformBag.readRefines p n q) :
    ∀ᵐ u ∂DyadicPosterior.law q,
      (UniformBag.rank (q.take n) : ℝ) / 2 ^ n ≤ u ∧
      u ≤ ((UniformBag.rank (q.take n) : ℝ) + 1) / 2 ^ n := by
  have hn : n ≤ q.length := by rw [hread.2]; exact le_max_right _ _
  have hprefix : q.take n <+: q := List.take_prefix _ _
  have habs := DyadicPosterior.law_refines hprefix
  have hcell := habs.ae_le (DyadicPosterior.ae_mem_cell (q.take n))
  filter_upwards [hcell] with u hu
  rw [cell_eq_rank] at hu
  simp only [List.length_take, Nat.min_eq_left hn, mem_Ico] at hu
  exact ⟨hu.1, hu.2.le⟩

end

end SampLib.LatentUniform
