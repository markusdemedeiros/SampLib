import SampLib.Latent.Syntax.PSRNDigits

/-! # Conditional digit callbacks retain their free variables -/

open ProbLang

namespace SampLib.LatentDigits.Syntax

open scoped SampLib.LatentDigits.Syntax

theorem read_fv {rT : Type} (nextBit : Val rT) :
    (readVal nextBit).fst.fv = nextBit.fst.fv := by
  simp [readVal, readCode, bind_fv, Exp.fv, ClosedExp.fv]

theorem oracle_fv {rT : Type} (nextBit : Val rT) (root : Loc) :
    (oracleVal nextBit root).fst.fv = nextBit.fst.fv := by
  simp [oracleVal, oracleCode, bind_fv, Exp.fv, read_fv]

end SampLib.LatentDigits.Syntax
