import SampLib.Bernoulli.Syntax.EnvelopeFactory

/-! # Unfolding the envelope factory source

Each lemma unfolds one source step of the envelope factory in a total weakest precondition.
The closedness certificates from the source module make each step a single pure reduction.
-/

open ProbLang

namespace SampLib.EnvelopeFactory.Program

open FactoryFractions

section opening

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

private theorem twp_unfold (E : CoPset) (K : Ectx rT) (body : Exp rT) (v : Val rT)
    (hc : (Exp.fix body).IsLocallyClosed) (Φ : Val rT → IProp GF) :
    tglWp E (K.fill (.app (Exp.open' body (.fix body)) v.fst)) Φ ⊢
      tglWp E (K.fill (.app (.fix body) v.fst)) Φ :=
  twp_pure_step_ctx K (v.fst.isValue ∧ (Exp.fix body).IsLocallyClosed) ⟨⟨v.snd⟩, hc⟩

/-- Unfold one source round using cached local-closedness certificates. -/
theorem twp_open_round (E : CoPset) (coin bounds next : Val rT) (l : Loc)
    (n heads : ℕ) (lo hi : Fraction) (Φ : Val rT → IProp GF) :
    tglWp E (round coin bounds next l n heads lo hi) Φ ⊢
      tglWp E (call coin bounds next l n heads lo hi) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill
      [.appL (Val.int (heads : ℤ)), .appL lo.encode, .appL hi.encode]
      (.app (.fix (fixBody coin bounds next l)) (Val.int (n : ℤ)).fst)) Φ)
  iapply (twp_unfold E
    [.appL (Val.int (heads : ℤ)), .appL lo.encode, .appL hi.encode]
    (fixBody coin bounds next l) (Val.int (n : ℤ)) (loop_lc coin bounds next l) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill
      [.appL (Val.int (heads : ℤ)), .appL lo.encode, .appL hi.encode]
      (.app (Exp.open' (fixBody coin bounds next l) (loop coin bounds next l))
        (Val.int (n : ℤ)).fst)) Φ)
  rw [opened_fix]
  iapply (twp_beta E [.appL (Val.int (heads : ℤ)), .appL lo.encode, .appL hi.encode]
    (nBody coin bounds next l) (Val.int (n : ℤ)) (nBody_lc coin bounds next l) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill
      [.appL (Val.int (heads : ℤ)), .appL lo.encode, .appL hi.encode]
      (Exp.open' (nBody coin bounds next l) (Val.int (n : ℤ)).fst)) Φ)
  rw [opened_n]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL lo.encode, .appL hi.encode]
      (.app (.lam (headsBody coin bounds next l n)) (Val.int (heads : ℤ)).fst)) Φ)
  iapply (twp_beta E [.appL lo.encode, .appL hi.encode]
    (headsBody coin bounds next l n) (Val.int (heads : ℤ)) (headsBody_lc coin bounds next l n) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL lo.encode, .appL hi.encode]
      (Exp.open' (headsBody coin bounds next l n) (Val.int (heads : ℤ)).fst)) Φ)
  rw [opened_heads]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL hi.encode]
      (.app (.lam (lowerBody coin bounds next l n heads)) lo.encode.fst)) Φ)
  iapply (twp_beta E [.appL hi.encode] (lowerBody coin bounds next l n heads) lo.encode
    (lowerBody_lc coin bounds next l n heads) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL hi.encode]
      (Exp.open' (lowerBody coin bounds next l n heads) lo.encode.fst)) Φ)
  rw [opened_lower]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (upperBody coin bounds next l n heads lo)) hi.encode.fst)) Φ)
  iapply (twp_beta E [] (upperBody coin bounds next l n heads lo) hi.encode
    (upperBody_lc coin bounds next l n heads lo) Φ)
  ieval (
    change _ ⊢ tglWp E (Exp.open' (upperBody coin bounds next l n heads lo) hi.encode.fst) Φ)
  rw [opened_upper]
  iexact H

/-- Open the four public arguments, leaving allocation to the caller's program proof. -/
theorem twp_open_initialization (E : CoPset) (coin bounds next : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E (initialization coin bounds next) Φ ⊢
      tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
        &coin.fst &bounds.fst &next.fst #()) Φ := by
  rw [source_eq]
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL bounds, .appL next, .appL Val.unit]
      (.app (.lam sourceBody) coin.fst)) Φ)
  iapply (twp_beta E [.appL bounds, .appL next, .appL Val.unit] sourceBody coin source_lc Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL next, .appL Val.unit]
      (.app (.lam (boundsBody coin)) bounds.fst)) Φ)
  iapply (twp_beta E [.appL next, .appL Val.unit] (boundsBody coin) bounds
    (boundsBody_lc coin) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill [.appL Val.unit]
      (.app (.lam (nextBody coin bounds)) next.fst)) Φ)
  iapply (twp_beta E [.appL Val.unit] (nextBody coin bounds) next
    (nextBody_lc coin bounds) Φ)
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (unitBody coin bounds next)) Val.unit.fst)) Φ)
  iapply (twp_beta E [] (unitBody coin bounds next) Val.unit (unitBody_lc coin bounds next) Φ)
  ieval (change _ ⊢ tglWp E (Exp.open' (unitBody coin bounds next) Val.unit.fst) Φ)
  rw [opened_unit]
  iexact H

/-- Supply the allocated bag and open the source's initial recursive call. -/
theorem twp_open_bag (E : CoPset) (coin bounds next : Val rT) (l : Loc)
    (Φ : Val rT → IProp GF) :
    tglWp E (call coin bounds next l 0 0 (Fraction.ofRat 0) (Fraction.ofRat 1)) Φ ⊢
      tglWp E (.app (.lam (bagBody coin bounds next)) (Val.loc l).fst) Φ := by
  iintro H
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (bagBody coin bounds next)) (Val.loc l).fst)) Φ)
  iapply (twp_beta E [] (bagBody coin bounds next) (Val.loc l)
    (bagBody_lc coin bounds next) Φ)
  ieval (change _ ⊢ tglWp E (Exp.open' (bagBody coin bounds next) (Val.loc l).fst) Φ)
  rw [opened_bag]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam initialCall) (loopValue coin bounds next l).fst)) Φ)
  iapply (twp_beta E [] initialCall (loopValue coin bounds next l)
    (by unfold initialCall; is_lc) Φ)
  ieval (
    change _ ⊢ tglWp E (call coin bounds next l 0 0 (Fraction.ofRat 0) (Fraction.ofRat 1)) Φ)
  iexact H

end opening

end SampLib.EnvelopeFactory.Program
