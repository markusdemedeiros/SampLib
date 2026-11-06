module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.List.Infix

@[expose] public section

/-! # Ranks and read extents of cached binary prefixes -/

namespace SampLib.UniformBag

/-- Binary place value of a finite prefix, with its first bit most significant. -/
def rank : List Bool → ℤ
  | [] => 0
  | b :: p => (if b then 1 else 0) * 2 ^ p.length + rank p

/-- Reading extends the existing cache only as far as necessary. -/
def readRefines (p : List Bool) (n : ℕ) (q : List Bool) : Prop :=
  p <+: q ∧ q.length = max p.length n

end SampLib.UniformBag
