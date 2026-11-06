import Samplers.Weighted.Optimal
import Metrology.ProbLang.Interp.BigStepIO

/-! Actual upstream substitution-interpreter regression, to run after the approved repair.
The original failing fixture and its log remain immutable in the parent directory. -/

open ProbLang

private def ints (xs : List ℤ) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair (.lit (.int x)) tail)) (.inl (.lit .unit))

private def table (rows : List ℤ) (k l rejected : ℤ) : Exp Float :=
  .pair (ints rows) (.pair (.lit (.int k)) (.pair (.lit (.int l)) (.lit (.int rejected))))

private structure Case where
  name : String
  weights : List ℤ
  rows : List ℤ
  k : ℤ
  l : ℤ
  rejected : ℤ
  support : List ℤ

private def controls : List Case := [
  ⟨"certain-left", [2, 0], [3, 0], 2, 1, -1, [0]⟩,
  ⟨"certain-right", [0, 2], [0, 3], 2, 1, -1, [1]⟩,
  ⟨"certain-interior-zeros", [0, 0, 6, 0, 0], [0, 0, 7, 0, 0], 3, 1, -1, [2]⟩,
  ⟨"certain-power-four", [0, 4, 0], [0, 7, 0], 3, 2, -1, [1]⟩,
  ⟨"certain-total-one", [0, 1, 0], [0, 1, 0], 1, 0, -1, [1]⟩,
  ⟨"certain-unchanged-period", [3, 0], [3, 0], 2, 0, -1, [0]⟩,
  ⟨"certain-with-rejection", [0, 5, 0, 0], [0, 6, 0, 0, 1], 3, 1, 4, [1]⟩,
  ⟨"singleton", [6], [7], 3, 1, -1, [0]⟩,
  ⟨"balanced", [1, 1], [2, 2], 2, 1, -1, [0, 1]⟩,
  ⟨"balanced-with-zeros", [0, 2, 0, 2], [0, 4, 0, 4], 3, 2, -1, [1, 3]⟩,
  ⟨"unequal-without-rejection", [1, 2], [1, 2], 2, 0, -1, [0, 1]⟩,
  ⟨"unequal-with-rejection", [1, 4], [1, 5, 1], 3, 1, 2, [0, 1]⟩,
  ⟨"unequal-rejection-and-zeros", [0, 1, 0, 4, 0], [0, 1, 0, 5, 0, 1],
    3, 1, 5, [1, 3]⟩]

/-- Every certain position at each tested length, including a rejected-mass control. -/
private def zeroPlacements : List Case :=
  (List.range 5).flatMap fun z =>
    let n := z + 1
    (List.range n).flatMap fun index =>
      ([(1, 1, 1, 0, false), (2, 3, 2, 1, false), (3, 3, 2, 0, false),
        (5, 6, 3, 1, true), (8, 15, 4, 3, false)] : List (ℤ × ℤ × ℤ × ℤ × Bool)).map
        fun (total, encoded, k, l, reject) =>
          let weights := (List.range n).map fun j => if j = index then total else 0
          let rows := (List.range n).map fun j => if j = index then encoded else 0
          ⟨s!"certain-total{total}-length{n}-position{index}", weights,
            if reject then rows ++ [1] else rows, k, l,
            if reject then (n : ℤ) else -1, [(index : ℤ)]⟩

private def cases : List Case := controls ++ zeroPlacements

private def bounded (fuel steps : ℕ) (c : Comp Float (Cfg Float) (Cfg Float))
    (ks : Array (Cfg Float → Comp Float (Cfg Float) (Cfg Float))) :
    IO (Option (Cfg Float) × ℕ) := do
  match fuel with
  | 0 => return (none, steps)
  | fuel + 1 =>
    match c with
    | .call x => bounded fuel (steps + 1) (bigStepF Interp.compOps .call x) ks
    | .bind c k => bounded fuel (steps + 1) c (ks.push k)
    | .ret r => match ks.back? with
      | none => return (some r, steps + 1)
      | some k => bounded fuel (steps + 1) (k r) ks.pop
    | .stuck msg => throw (IO.userError msg)
    | .sample z k => bounded fuel (steps + 1) (k (← Interp.sampleInt z)) ks
    | .sampleReal k => bounded fuel (steps + 1) (k (← Interp.sampleUnit)) ks

private def check (test : Case) (profile : Bool := false) : IO Unit := do
  let actual ← Interp.eval pl(&Occil.WeightedVariants.optimalMatrix &(ints test.weights))
  let expected := table test.rows test.k test.l test.rejected
  unless actual == expected do
    throw (IO.userError s!"{test.name}: wrong matrix\nactual {reprStr actual}\nexpected {reprStr expected}")
  for (sampler, program) in [
      ("optimalChoice", pl(&Occil.WeightedVariants.optimalChoice &(ints test.weights) #())),
      ("optimalDraw", pl(&Occil.WeightedVariants.optimalDraw &actual #()))] do
    for seed in [0, 1, 99] do
      IO.setRandSeed seed
      let (result, steps) ← bounded 100000 0 (.call ⟨program, default⟩) #[]
      let some cfg := result
        | throw (IO.userError s!"{test.name}: {sampler} exhausted {steps} transitions at seed {seed}")
      if profile then IO.println s!"PROFILE {test.name}: {sampler}, seed={seed}, transitions={steps}"
      match cfg.expr with
      | .lit (.int value) =>
        unless value ∈ test.support do
          throw (IO.userError s!"{test.name}: {sampler} returned {value} at seed {seed}, support {test.support}")
      | expr => throw (IO.userError s!"{test.name}: {sampler} returned {reprStr expr}")
  IO.println s!"PASS {test.name}: rows={test.rows}, k={test.k}, l={test.l}, reject={test.rejected}, support={test.support}"

def main (args : List String) : IO Unit := do
  if "--profile" ∈ args then
    check ⟨"certain-interior-zeros", [0, 0, 6, 0, 0], [0, 0, 7, 0, 0],
      3, 1, -1, [2]⟩ true
  else
    for test in cases do check test
    IO.println s!"PASS all {cases.length} matrix checks and {6 * cases.length} bounded actual-sampler runs"
