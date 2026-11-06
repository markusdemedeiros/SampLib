import SampLib.Syntax.OptimalWalk
import SampLib.Distributions.OptimalMatrixData

/-! # The original cyclic table representation and direct-draw source -/

open ProbLang

namespace SampLib.OptimalMatrix.Table

/-- The source tuple contains the matrix, width, cycle start, and rejection label. -/
def value {rT : Type} [ProbLangℝ rT] (t : OptimalMatrix.Table) : Val rT :=
  Val.pair (listVal (fun m : ℕ => Val.int m) t.rows)
    (Val.pair (Val.int t.width) (Val.pair (Val.int t.loopStart) (Val.int t.rejected)))

end SampLib.OptimalMatrix.Table

namespace SampLib.Optimal.Program

@[pl_fold] def drawSource {rT : Type} : Exp rT := pl%
  fun table u,
    let matrix := fst(table);
    let k := fst(snd(table));
    let l := fst(snd(snd(table)));
    let rejected := snd(snd(snd(table)));
    let scan := &scan;
    let walk := (rec draw value column :=
      let expanded := #2 * value + rand(#2, #());
      let outcome := scan matrix expanded (k - #1 - column) #0;
      if fst(outcome) then
        if snd(outcome) = rejected then draw #0 #0 else snd(outcome)
      else draw (snd(outcome)) (if column + #1 = k then l else column + #1));
    walk #0 #0

theorem draw_source_eq {rT : Type} :
    (Occil.WeightedVariants.optimalDraw : Exp rT) = drawSource := by kernel_rfl

end SampLib.Optimal.Program
