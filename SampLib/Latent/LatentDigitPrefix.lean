import SampLib.Latent.LatentDigitModel

/-! # Prefix arithmetic for conditional digit reads -/

namespace SampLib.LatentDigits

open MeasureTheory

theorem rank_append (p q : List Bool) :
    UniformBag.rank (p ++ q) =
      UniformBag.rank p * 2 ^ q.length + UniformBag.rank q := by
  induction p with
  | nil => simp [UniformBag.rank]
  | cons b p ih =>
    simp only [List.cons_append, UniformBag.rank, List.length_append, pow_add, ih]
    ring

@[simp] theorem rank_extend (p : List Bool) (b : Bool) :
    UniformBag.rank (p ++ [b]) = UniformBag.rank p * 2 + if b then 1 else 0 := by
  simp [rank_append, UniformBag.rank]

variable {Ω : Type} [MeasurableSpace Ω]

/-- Reattach the observed head after recursively reading the retained tail. -/
theorem readRefines_step {p cached q : List Bool} {b : Bool} {n : ℕ}
    (hs : UniformBag.stepRefines p b cached) (hr : UniformBag.readRefines cached n q) :
    UniformBag.readRefines p (n + 1) (b :: q) := by
  rcases hr with ⟨hp, hlen⟩
  rcases hs with ⟨rfl, rfl⟩ | rfl
  · exact ⟨List.nil_prefix, by simp_all⟩
  · exact ⟨List.cons_prefix_cons.mpr ⟨rfl, hp⟩, by
      simp only [List.length_cons]
      omega⟩

/-- The interval accumulated after traversing `n` more digits. -/
def readInterval (processed cached : List Bool) (n : ℕ) : LatentReal.RationalInterval where
  lower := UniformBag.rank processed * 2 ^ n + UniformBag.rank (cached.take n)
  upper := UniformBag.rank processed * 2 ^ n + UniformBag.rank (cached.take n) + 1
  denominator := 2 ^ (processed.length + n)
  denominator_pos := pow_pos (by norm_num) _
  lower_le_upper := by omega

@[simp] theorem readInterval_nil (cached : List Bool) (n : ℕ) :
    readInterval [] cached n = LatentUniform.interval cached n := by
  simp [readInterval, LatentUniform.interval, UniformBag.rank]

/-- Advancing one digit changes only the representation of the same final interval. -/
theorem readInterval_advance (processed q : List Bool) (b : Bool) (n : ℕ)
    (hn : n ≤ q.length) :
    readInterval (processed ++ [b]) q n = readInterval processed (b :: q) (n + 1) := by
  have hr : UniformBag.rank (processed ++ [b]) * 2 ^ n +
      UniformBag.rank (q.take n) =
      UniformBag.rank processed * 2 ^ (n + 1) + UniformBag.rank ((b :: q).take (n + 1)) := by
    simp only [rank_extend, List.take_succ_cons, UniformBag.rank, List.length_take,
      Nat.min_eq_left hn, pow_succ]
    ring
  have hd : (processed ++ [b]).length + n = processed.length + (n + 1) := by simp; omega
  simp only [readInterval, hr, hd]

end SampLib.LatentDigits
