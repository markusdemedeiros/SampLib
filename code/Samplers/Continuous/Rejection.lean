import Samplers.Uniform

/-! Generic proposal-and-acceptance rejection sampling. -/
namespace Occil

open ProbLang

variable {rT : Type _}

/-- Generic rejection: requires positive acceptance probability and fresh proposals. -/
@[pl_fold] def rejection : Exp rT := pl%
  rec draw proposal accept u :=
    let x := proposal #();
    if accept x then x else draw proposal accept #()

end Occil
