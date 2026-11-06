import SampLib.Common.Laws.WordIntervals

/-! # Equal accepted fibres of multiply-high reduction

Writing the source width as `n*q+t`, the accepted source words for output `y`
form the interval starting at `q*y+ceil(t*(y+1)/n)`, of length exactly `q`.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace SampLib.MultiplyHigh

noncomputable section

def ceiling (n x : ℕ) : ℕ := (x + n - 1) / n

theorem ceiling_bounds (n x : ℕ) (hn : 0 < n) :
    x ≤ n * ceiling n x ∧ n * ceiling n x < x + n := by
  have hr := Nat.mod_lt (x + n - 1) hn
  have heq := Nat.mod_add_div (x + n - 1) n
  dsimp [ceiling]
  omega

def start (n width y : ℕ) : ℕ :=
  (width / n) * y + ceiling n (width % n * (y + 1))

/-- An accepted output fibre is a consecutive interval of the Euclidean quotient length. -/
theorem fibre (n width y r : ℕ) (hn : 0 < n) (hnw : n ≤ width) (hy : y < n) :
    (r < width ∧ n * r / width = y ∧ width % n ≤ n * r % width) ↔
      start n width y ≤ r ∧ r < start n width y + width / n := by
  let q := width / n
  let t := width % n
  let s := ceiling n (t * (y + 1))
  have hw : 0 < width := lt_of_lt_of_le hn hnw
  have heq : t + n * q = width := Nat.mod_add_div width n
  have heqy : (t + n * q) * y = width * y := congrArg (fun a => a * y) heq
  have hs := ceiling_bounds n (t * (y + 1)) hn
  change t * (y + 1) ≤ n * s ∧ n * s < t * (y + 1) + n at hs
  change (r < width ∧ n * r / width = y ∧ t ≤ n * r % width) ↔
    q * y + s ≤ r ∧ r < q * y + s + q
  constructor
  · rintro ⟨hr, hyq, ht⟩
    have hrem := Nat.mod_lt (n * r) hw
    have hrepr := Nat.mod_add_div (n * r) width
    rw [hyq] at hrepr
    constructor <;> nlinarith
  · rintro ⟨hlo, hhi⟩
    have hlo' : y * width ≤ n * r := by nlinarith
    have hhi' : n * r < (y + 1) * width := by nlinarith
    have hquot : n * r / width = y := Nat.div_eq_of_lt_le hlo' hhi'
    have hrepr := Nat.mod_add_div (n * r) width
    rw [hquot] at hrepr
    exact ⟨by nlinarith, hquot, by nlinarith⟩

def accepted (n width : ℕ) : Finset ℕ :=
  (range width).filter (fun r => width % n ≤ n * r % width)

theorem accepted_fibre (n width y : ℕ) (hn : 0 < n) (hnw : n ≤ width) (hy : y < n) :
    (accepted n width).filter (fun r => n * r / width = y) =
      Ico (start n width y) (start n width y + width / n) := by
  ext r
  simp only [accepted, mem_filter, mem_range, mem_Ico]
  simpa only [and_assoc, and_left_comm, and_comm] using fibre n width y r hn hnw hy

/-- Every output fibre contains exactly `width/n` accepted words. -/
theorem sum_accepted (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width)
    (F : ℕ → ℝ≥0∞) :
    ∑ r ∈ accepted n width, F (n * r / width) =
      (width / n : ℕ) * ∑ y ∈ range n, F y := by
  have hw : 0 < width := lt_of_lt_of_le hn hnw
  have hmaps (r : ℕ) (hr : r ∈ accepted n width) : n * r / width ∈ range n := by
    have hr' : r < width := (mem_filter.mp hr).1 |> mem_range.mp
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hw).2
      (Nat.mul_lt_mul_of_pos_left hr' hn))
  calc
    _ = ∑ y ∈ range n, ∑ r ∈ (accepted n width).filter
        (fun r => n * r / width = y), F y := (sum_fiberwise_of_maps_to' hmaps F).symm
    _ = ∑ y ∈ range n, (width / n : ℕ) * F y := by
      apply sum_congr rfl
      intro y hy
      rw [accepted_fibre n width y hn hnw (mem_range.mp hy)]
      simp [nsmul_eq_mul]
    _ = _ := (mul_sum ..).symm

theorem card_accepted (n width : ℕ) (hn : 0 < n) (hnw : n ≤ width) :
    (accepted n width).card = n * (width / n) := by
  have h := sum_accepted n width hn hnw (fun _ => 1)
  have hcast : ((accepted n width).card : ℝ≥0∞) = (n * (width / n) : ℕ) := by
    simpa [nsmul_eq_mul, mul_comm] using h
  exact_mod_cast hcast

end

end SampLib.MultiplyHigh
