import Samplers.Uniform

/-! Bounded independent-trial count sampling. -/
namespace Occil

open ProbLang

variable {rT : Type _}

/-- Bounded failures before success (the direct trial variant). Unlike capping
an unbounded geometric, this also terminates when p=0. -/
@[pl_fold] def boundedGeometric : Exp rT := pl%
  rec draw coin bound := if bound < #0 then fail else if bound = #0 then #0 else
    if coin #() then #0 else #1 + draw coin (bound - #1)

end Occil
