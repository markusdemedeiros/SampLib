import Samplers.Weighted.Optimal
import Metrology.ProbLang.Interp.BigStepIO

/-! A fuel limit around the upstream substitution interpreter, not a host sampler. -/

open ProbLang

private def ints (xs : List ℤ) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair (.lit (.int x)) tail)) (.inl (.lit .unit))

private def bounded (fuel : ℕ) (c : Comp Float (Cfg Float) (Cfg Float))
    (ks : Array (Cfg Float → Comp Float (Cfg Float) (Cfg Float))) : IO (Option (Cfg Float)) := do
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match c with
    | .call x => bounded fuel (bigStepF Interp.compOps .call x) ks
    | .bind c k => bounded fuel c (ks.push k)
    | .ret r => match ks.back? with
      | none => return some r
      | some k => bounded fuel (k r) ks.pop
    | .stuck msg => throw (IO.userError msg)
    | .sample z k => bounded fuel (k (← Interp.sampleInt z)) ks
    | .sampleReal k => bounded fuel (k (← Interp.sampleUnit)) ks

private def result (r : Option (Cfg Float)) : String :=
  match r with
  | none => "fuel exhausted"
  | some r => reprStr r.expr

def main : IO Unit := do
  let table ← Interp.eval pl(&Occil.WeightedVariants.optimalMatrix &(ints [2, 0]))
  IO.println s!"optimalMatrix [2,0]: {reprStr table}"
  for seed in [0, 1, 99] do
    IO.setRandSeed seed
    let bad ← bounded 10000 (.call ⟨pl(&Occil.WeightedVariants.optimalChoice
      &(ints [2, 0]) #()), default⟩) #[]
    IO.println s!"optimalChoice [2,0], seed {seed}, 10000 Comp transitions: {result bad}"
  IO.setRandSeed 0
  let good ← bounded 10000 (.call ⟨pl(&Occil.WeightedVariants.optimalChoice
    &(ints [1, 1]) #()), default⟩) #[]
  IO.println s!"control optimalChoice [1,1], 10000 Comp transitions: {result good}"
