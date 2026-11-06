import SampLib.LatentSpec

/-! # The expanding and bisecting loops of the deferred root oracle -/

open ProbLang

namespace SampLib.LatentReal.Root.Program

/-- The source doubles an upper bound until the callback resolves it. -/
def bracketCode {rT : Type} (below : Exp rT) : Exp rT :=
  .fix (.lam (.cond (.app below (.bvar 0)) (.bvar 0)
    (.app (.bvar 1) (.binop .mult (.bvar 0) (.lit (.int 2))))))

def bracket {rT : Type} (below : Val rT) : Exp rT := bracketCode below.fst

/-- Bisection stops at adjacent integer endpoints, retaining the fixed denominator. -/
def bisectCode {rT : Type} (below : Exp rT) (denominator : ℤ) : Exp rT :=
  let stop := .binop .le (.binop .minus (.bvar 0) (.bvar 1)) (.lit (.int 1))
  let result := .pair (.bvar 1) (.pair (.bvar 0) (.lit (.int denominator)))
  let lower := .app (.app (.bvar 3) (.bvar 2)) (.bvar 0)
  let upper := .app (.app (.bvar 3) (.bvar 0)) (.bvar 1)
  let mid := .binop .div (.binop .plus (.bvar 1) (.bvar 0)) (.lit (.int 2))
  let step := .app (.lam (.cond (.app below (.bvar 0)) lower upper)) mid
  .fix (.lam (.lam (.cond stop result step)))

def bisect {rT : Type} (below : Val rT) (denominator : ℤ) : Exp rT :=
  bisectCode below.fst denominator

/-- A fixed callback remains locally closed underneath both bisection arguments. -/
theorem bisect_lc {rT : Type} (below : Val rT) (denominator : ℤ) :
    (bisect below denominator).IsLocallyClosed := by
  apply Exp.lcb_imp_lc
  have hb (k : ℕ) : Exp.lcb k below.fst = true :=
    Exp.lcb_mono (Exp.lc_imp_lcb below.lc) (Nat.zero_le k)
  simp [bisect, bisectCode, Exp.lcb, hb]

end SampLib.LatentReal.Root.Program
