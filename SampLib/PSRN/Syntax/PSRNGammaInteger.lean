import SampLib.Core.Syntax.ClosedExp
import SampLib.Core.CurriedStep
import Samplers.PSRN.BetaGamma

/-! # Closed source gateways for the recursive integer-gamma constructor -/

open ProbLang

namespace SampLib.PSRNGammaInteger.Program

scoped instance exponential_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newExponential : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance add_closed {rT : Type} : ClosedExp (Occil.PSRN.add : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

open scoped SampLib.PSRNGammaInteger.Program

/-- Exact recursive syntax with the exponential gateway kept named under binders. -/
def gammaCode {rT : Type} : Exp rT :=
  .fix (.lam (.lam (.lam
    (.cond (.binop .le (.bvar 2) (.lit (.int 0))) .fail
      (.app (.lam
        (.cond (.binop .eq (.bvar 3) (.lit (.int 1))) (.bvar 0)
          (.app (.app Occil.PSRN.add (.bvar 0))
            (.app (.app (.app (.bvar 4)
              (.binop .minus (.bvar 3) (.lit (.int 1)))) (.bvar 2)) (.bvar 1)))))
        (.app (.app (.app Occil.PSRN.newExponential (.bvar 1)) (.bvar 0)) (.lit .unit)))))))

theorem source_eq_code {rT : Type} : (Occil.PSRN.newGammaInteger : Exp rT) = gammaCode := by
  simp [Occil.PSRN.newGammaInteger, gammaCode, Exp.close, Exp.closeRec,
    ClosedExp.closeRec, Var.internal.injEq]

scoped instance gamma_closed {rT : Type} :
    ClosedExp (Occil.PSRN.newGammaInteger : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

scoped instance code_closed {rT : Type} : ClosedExp (gammaCode : Exp rT) := by
  rw [← source_eq_code]
  infer_instance

/-- The final source branch, after its predecessor arithmetic is evaluated. -/
def addNext {rT : Type} (next a b : ℤ) (left : Val rT) : Exp rT :=
  pl(&Occil.PSRN.add &left.fst (&gammaCode #next #a #b))

def recursiveBranch {rT : Type} (n : ℕ) (a b : ℤ) (left : Val rT) : Exp rT :=
  addNext (((n + 1 + 1 : ℕ) : ℤ) - 1) a b left

theorem recursiveBranch_eq {rT : Type} (n : ℕ) (a b : ℤ) (left : Val rT) :
    recursiveBranch n a b left = addNext ((n + 1 : ℕ) : ℤ) a b left := by
  unfold recursiveBranch
  have h : (((n + 1 + 1 : ℕ) : ℤ) - 1) = ((n + 1 : ℕ) : ℤ) := by omega
  rw [h]

end SampLib.PSRNGammaInteger.Program
