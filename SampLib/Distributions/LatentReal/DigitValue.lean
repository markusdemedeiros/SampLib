import SampLib.Distributions.LatentReal.BinaryExpansion
import SampLib.Distributions.LatentReal.Uniform

/-! # Closed dyadic enclosures of arbitrary binary streams -/

open Set MeasureTheory

namespace SampLib.DigitPosterior

noncomputable section

/-- A cached prefix fixes the affine coordinates of the same latent real. -/
theorem value_eq_embed {Ω : Type} (digits : Ω → ℕ → Bool) (p : List Bool) {x : Ω}
    (hx : x ∈ cylinder digits p) :
    value (digits x) =
      DyadicPosterior.embed p (value (fun n => digits x (n + p.length))) := by
  induction p generalizing digits with
  | nil => simp [DyadicPosterior.embed]
  | cons b p ih =>
    rcases hx with ⟨hb, hp⟩
    rw [value_shift, hb, ih (fun x n => digits x (n + 1)) hp]
    simp only [DyadicPosterior.embed, List.length_cons]
    congr 2

/-- Every stream in a finite cylinder lies in its closed dyadic interval. -/
theorem value_mem_interval {Ω : Type} (digits : Ω → ℕ → Bool) (p : List Bool) {x : Ω}
    (hx : x ∈ cylinder digits p) :
    (UniformBag.rank p : ℝ) / 2 ^ p.length ≤ value (digits x) ∧
      value (digits x) ≤ ((UniformBag.rank p : ℝ) + 1) / 2 ^ p.length := by
  rw [value_eq_embed digits p hx, LatentUniform.embed_eq_rank]
  have h0 := value_nonneg (fun n => digits x (n + p.length))
  have h1 := value_le_one (fun n => digits x (n + p.length))
  constructor
  · gcongr
    linarith
  · gcongr

/-- Posterior enclosures remain valid when reads request fewer digits than the cache holds. -/
theorem ae_read_interval {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    {digits : Ω → ℕ → Bool} (hd : ∀ n, Measurable (fun x => digits x n))
    {p q : List Bool} {n : ℕ} (hread : UniformBag.readRefines p n q) :
    ∀ᵐ x ∂law μ digits q,
      (UniformBag.rank (q.take n) : ℝ) / 2 ^ n ≤ value (digits x) ∧
        value (digits x) ≤ ((UniformBag.rank (q.take n) : ℝ) + 1) / 2 ^ n := by
  have hn : n ≤ q.length := by rw [hread.2]; exact le_max_right _ _
  filter_upwards [ae_mem μ hd q] with x hx
  have h := value_mem_interval digits (q.take n)
    (cylinder_mono (List.take_prefix n q) hx)
  simpa only [List.length_take, Nat.min_eq_left hn] using h

end

end SampLib.DigitPosterior
