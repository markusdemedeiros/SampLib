import SampLib.General.CFTPDeterministic

/-! # The CFTP loop with finalized binders

The callback remains a locally closed value leaf. The constructors reproduce the
source loop without closing over arbitrary callback free variables.
-/

open ProbLang

namespace SampLib.CouplingFromPast

@[pl_fold] def run {rT : Type _} (size : ℕ) (sample : Val rT) : Exp rT :=
  .fix (.lam (.lam (.app
    (.lam (.app
      (.lam (.cond (.app (.bvar 0) (.lit (.int 1))) (.bvar 1)
        (.app (.lam
          (.app (.app (.bvar 5) (.binop .mult (.bvar 4) (.lit (.int 2))))
            (.app (.app Occil.General.append (.bvar 0)) (.bvar 3))))
          (.app (.app Occil.repeatSample sample.fst) (.bvar 3)))))
      (.fix (.lam (.cond (.binop .le (.lit (.int size)) (.bvar 0)) (.lit (.bool true))
        (.cond (.binop .eq
          (.app (.app Occil.General.applyMaps (.bvar 3)) (.bvar 0)) (.bvar 2))
          (.app (.bvar 1) (.binop .plus (.bvar 0) (.lit (.int 1))))
          (.lit (.bool false))))))))
    (.app (.app Occil.General.applyMaps (.bvar 0)) (.lit (.int 0))))))

theorem run_lc {rT : Type _} (size : ℕ) (sample : Val rT) :
    (run size sample).IsLocallyClosed := by is_lc

theorem run_openRec {rT : Type _} (size : ℕ) (sample : Val rT) (k : ℕ) (e : Exp rT) :
    Exp.openRec k e (run size sample) = run size sample :=
  (Exp.open_lc k e _ (run_lc size sample)).symm

/-- The source continuation after a failed finite coalescence check. -/
@[pl_fold] def extend {rT : Type _} [ProbLangℝ rT] {n : ℕ} (sample : Val rT)
    (h : ℕ) (maps : List (Map n)) : Exp rT :=
  .app (.lam (.app
    (.app (run n sample) (.binop .mult (.lit (.int h)) (.lit (.int 2))))
    (.app (.app Occil.General.append (.bvar 0)) (mapsVal maps).fst)))
    (.app (.app Occil.repeatSample sample.fst) (.lit (.int h)))

end SampLib.CouplingFromPast
