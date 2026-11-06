import Samplers.PSRN.Exponential
import SampLib.Samplers.Geometric

/-! # The literal integer-part loop in the decay-based exponential constructor -/

open ProbLang

namespace SampLib.ExponentialCount.Program

/-- Insert the decay expression at its actual lexical depth. -/
def countCode {rT : Type} (decay : Exp rT) : Exp rT :=
  .fix (.lam (.cond (.app decay (.lit (.int 1)))
    (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1)))) (.bvar 0)))

private theorem count_lc {rT : Type} (decay : Val rT) :
    (countCode decay.fst).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hd (k : ℕ) : Exp.lcb k decay.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb decay.lc) (Nat.zero_le k)
  simp [countCode, Exp.lcb, hd]

/-- The actual counter closure, without any free-variable restriction on the callback. -/
def countVal {rT : Type} (decay : Val rT) : Val rT :=
  ⟨countCode decay.fst, .fix (count_lc decay), count_lc decay⟩

end SampLib.ExponentialCount.Program
