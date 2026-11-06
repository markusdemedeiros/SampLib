import SampLib.Distributions.OptimalParameters
import SampLib.Distributions.OptimalCredits

/-! # The exact table produced from a full nonnegative weight vector -/

open scoped ENNReal

namespace SampLib.OptimalMatrix

open OptimalEncoding

/-- Padding is an ordinary last row; original zero-weight positions are retained. -/
def values (ws : List ℕ) (D : ℕ) : List ℕ :=
  if D - ws.sum = 0 then ws else ws ++ [D - ws.sum]

def rejectionIndex (ws : List ℕ) (D : ℕ) : ℤ :=
  if D - ws.sum = 0 then -1 else ws.length

/-- The source's matrix and three integer traversal parameters. -/
structure Table where
  rows : List ℕ
  width : ℕ
  loopStart : ℕ
  rejected : ℤ

/-- Preprocessing uses the actual finite search, followed by the repaired encoder. -/
def create (ws : List ℕ) : Table :=
  let k := ws.sum.size
  let selected := OptimalParameters.selected ws.sum
  ⟨(values ws selected.2).map (binary k selected.1), k, selected.1,
    rejectionIndex ws selected.2⟩

theorem values_sum (ws : List ℕ) (D : ℕ) (hD : ws.sum ≤ D) : (values ws D).sum = D := by
  unfold values
  split_ifs with heq
  · omega
  · simp only [List.sum_append, List.sum_singleton]
    omega

theorem value_le (ws : List ℕ) (D m : ℕ) (hD : ws.sum ≤ D) (hm : m ∈ values ws D) :
    m ≤ D := by
  rw [← values_sum ws D hD]
  exact List.le_sum_of_mem hm

/-- A finite-index view of the exact encoded matrix, without changing row order. -/
def encoded (ws : List ℕ) (k l : ℕ) : Fin (values ws (denominator k l)).length → ℕ :=
  fun i => binary k l ((values ws (denominator k l)).get i)

theorem encoded_rows (ws : List ℕ) (k l : ℕ) :
    List.ofFn (encoded ws k l) = (values ws (denominator k l)).map (binary k l) := by
  unfold encoded
  simpa only [List.map_ofFn, Function.comp_def] using
    congrArg (List.map (binary k l)) (List.ofFn_get (values ws (denominator k l)))

/-- The normalized table presentation used for the general draw theorem. -/
def table (ws : List ℕ) (k l : ℕ) : Table :=
  ⟨(values ws (denominator k l)).map (binary k l), k, l,
    rejectionIndex ws (denominator k l)⟩

theorem create_eq_table (ws : List ℕ) (hs : 0 < ws.sum) :
    create ws = table ws ws.sum.size (OptimalParameters.selected ws.sum).1 := by
  have h := (OptimalParameters.selected_valid hs).2.1
  simp only [create, table, h]

private theorem values_fin_sum (ws : List ℕ) (D : ℕ) (hD : ws.sum ≤ D) :
    ∑ i, (values ws D).get i = D := by
  rw [← List.sum_ofFn, List.ofFn_get, values_sum ws D hD]

theorem encoded_root (ws : List ℕ) {k l : ℕ} (hl : l < k)
    (hD : ws.sum ≤ denominator k l) :
    ∑ i, OptimalCyclic.tail k l (encoded ws k l i) 0 = 1 :=
  OptimalCyclic.encoded_root hl (values ws (denominator k l)).get
    (values_fin_sum ws _ hD)

theorem encoded_row_credit (ws : List ℕ) {k l : ℕ} (hl : l < k)
    (hD : ws.sum ≤ denominator k l) (F : ℕ → ℝ≥0∞) :
    OptimalCyclic.rowCredit (encoded ws k l) k l 0 F =
      WeightedChoice.weightedSum (values ws (denominator k l)) F / denominator k l := by
  unfold encoded
  rw [OptimalCyclic.encoded_row_zero hl _ (values_fin_sum ws _ hD),
    ← KnuthYaoColumns.weightedSum_ofFn, List.ofFn_get]

/-- Choosing the bit length keeps the rejection probability at most one half. -/
theorem selected_le_twice {total : ℕ} (htotal : 0 < total) :
    (OptimalParameters.selected total).2 ≤ 2 * total := by
  have hk : 0 < total.size := Nat.size_pos.mpr htotal
  have hlow : 2 ^ (total.size - 1) ≤ total := Nat.lt_size.mp (by omega)
  have hceil : 2 ^ total.size ≤ 2 * total := by
    calc
      _ = 2 * 2 ^ (total.size - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ total.size)]
      _ ≤ 2 * total := Nat.mul_le_mul_left 2 hlow
  exact (OptimalParameters.selected_lt_ceiling htotal).le.trans hceil

end SampLib.OptimalMatrix
