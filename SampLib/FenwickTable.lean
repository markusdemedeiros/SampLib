import SampLib.ArrayVector
import SampLib.Distributions.Fenwick

/-! # Ownership of a mutable Fenwick table

The weights and all dyadic interval sums are owned together. A replacement may
leave total mass zero; positivity is required only when drawing a sample.
-/

open ProbLang Iris Iris.BI Iris.ProofMode

namespace SampLib.FenwickTable

abbrev natVal {rT : Type} [ProbLangℝ rT] (n : ℕ) : Val rT := .int n

def value {rT : Type} [ProbLangℝ rT] (n : ℕ) (total values tree : Loc) : Val rT :=
  .pair (.int n) (.pair (.loc total) (.pair (.loc values) (.loc tree)))

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF]
local bi (IProp GF)

/-- The zero-th tree cell is present and contains zero. -/
def owns {n : ℕ} (w : Fin n → ℕ) (total values tree : Loc) : IProp GF :=
  iprop(appHeapFrag total (natVal (List.ofFn w).sum) ∗
    Array.owns values (List.ofFn (natVal (rT := rT) ∘ w)) ∗
    Array.owns tree (List.ofFn (natVal (rT := rT) ∘
      (fun i : Fin (n + 1) => FenwickMath.cell w i.val))))

end SampLib.FenwickTable
