import SampLib.Distributions.FastLoadedDiceCredits
import SampLib.Distributions.FldrDyadic

/-! # Conditional column credits for FLDR's implicit padded row -/

open Finset
open scoped NNReal ENNReal

namespace SampLib.FastLoadedDiceScan

noncomputable section

open FastLoadedDiceCredits

def bits (xs : List ℕ) (place : ℕ) : List ℕ := xs.map (fun w => w / place % 2)

def dummy (P T place : ℕ) : ℕ := (P - T) / place % 2

/-- The original rows are followed by the one implicit rejection row. -/
def kernel (ws : List ℕ) (P place : ℕ) (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞)
    (next : ℕ → ℝ≥0∞) (xs : List ℕ) (d offset : ℕ) : ℝ≥0∞ :=
  DdgCredits.scan (bits xs place ++ [dummy P ws.sum place]) d
    (fun i => extended ws F ε (offset + i)) next

@[simp] theorem kernel_cons (ws : List ℕ) (P place : ℕ) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (next : ℕ → ℝ≥0∞) (w : ℕ) (xs : List ℕ) (d offset : ℕ) :
    kernel ws P place F ε next (w :: xs) d offset =
      if d < w / place % 2 then extended ws F ε offset
      else kernel ws P place F ε next xs (d - w / place % 2) (offset + 1) := by
  simp only [kernel, bits, List.map_cons, List.cons_append, DdgCredits.scan, Nat.add_zero]
  congr 1
  congr 1
  funext i
  congr 1
  omega

@[simp] theorem kernel_nil (ws : List ℕ) (P place : ℕ) (F : ℕ → ℝ≥0∞)
    (ε : ℝ≥0∞) (next : ℕ → ℝ≥0∞) (d : ℕ) :
    kernel ws P place F ε next [] d ws.length =
      if d < dummy P ws.sum place then credit ws F + 2 * ε
      else next (d - dummy P ws.sum place) := by
  simp [kernel, bits, DdgCredits.scan, extended]

/-- The explicit dyadic matrix and the source's implicit padding have identical columns. -/
theorem source_columns (ws : List ℕ) (k d : ℕ) (hd : d < k) :
    bits ws (FldrDyadic.place k d) ++ [dummy (2 ^ k) ws.sum (FldrDyadic.place k d)] =
      KnuthYaoColumns.columns (augmented ws (2 ^ k)).get (2 ^ k) d := by
  rw [KnuthYaoColumns.columns_list]
  simp only [augmented, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · apply List.map_congr_left
    intro w _
    exact FldrDyadic.digit w k d hd
  · exact congrArg List.singleton (FldrDyadic.digit (2 ^ k - ws.sum) k d hd)

end

end SampLib.FastLoadedDiceScan
