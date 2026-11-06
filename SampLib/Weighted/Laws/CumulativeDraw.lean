import SampLib.Common.Laws.FiniteCDF

/-! # The cumulative table of a finite CDF -/

namespace SampLib.CumulativeDraw

open FiniteCDF

/-- Store the CDF on its natural index grid, with no restriction on plateaus. -/
def cumulative (D : Model) (n : ℕ) : List ℤ :=
  List.ofFn (fun i : Fin n => D.cdf (i.val : ℤ))

end SampLib.CumulativeDraw
