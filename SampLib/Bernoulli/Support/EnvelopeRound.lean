import SampLib.Bernoulli.Support.EnvelopeCallbacks
import SampLib.Bernoulli.Support.EnvelopeState
import SampLib.Bernoulli.Syntax.EnvelopeFactory

/-! # Symbolic execution of the degree, binomial and coefficient prefix of one envelope round -/

open ProbLang
open scoped ENNReal

namespace SampLib.EnvelopeFactory

open FactoryFractions

noncomputable section

/-- Abstracting the recursive value keeps its local-closedness certificate opaque. -/
def roundWithSelf {rT : Type} (self coin bounds next : Val rT) (l : Loc)
    (n heads : ℕ) (lo hi : Fraction) : Exp rT :=
  Program.roundCode (fun _ => self.fst) (fun _ => coin.fst) (fun _ => bounds.fst)
    (fun _ => next.fst) (fun _ => (Val.loc l).fst)
    (fun _ => pl(#int (n : ℤ))) (fun _ => pl(#int (heads : ℤ)))
    (fun _ => lo.encode.fst) (fun _ => hi.encode.fst)

theorem round_eq_withSelf {rT : Type} (coin bounds next : Val rT) (l : Loc)
    (n heads : ℕ) (lo hi : Fraction) :
    Program.round coin bounds next l n heads lo hi =
      roundWithSelf (Program.loopValue coin bounds next l) coin bounds next l n heads lo hi := rfl

/-- Expose the conditional loop's small start term under its own binder for LC checking. -/
private theorem conditionalBody_explicit {rT : Type}
    (bounds n m k high : ℕ → Exp rT) :
    EnvelopeConditionalAverage.bodyCode bounds n m k high =
      let average := EnvelopeConditionalAverage.loopCode
        (fun d => bounds (d + 1)) (fun d => n (d + 1))
        (fun d => m (d + 1)) (fun d => k (d + 1)) (fun d => high (d + 1)) Exp.bvar
      .cond (.binop .eq (n 0) pl(#0)) (.cond (high 0) pl((#1, #1)) pl((#0, #1)))
        (.app (.lam (.app (.lam
          (.app (.app (.bvar 0) pl(#0)) pl((#0, #1)))) average))
          (.app (.app Occil.FactoryExtra.choose (m 0)) (k 0))) := rfl

private theorem degree_test (a : Coefficients) (t : ℕ) :
    decide ((a.degree (t + 1) : ℤ) ≤ a.degree t) = false :=
  decide_eq_false (by exact_mod_cast (not_le.mpr (a.grows t)))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local irreducible] FactoryFractions.encode FactoryFractions.Fraction.encode

/-- One fresh binomial block transports the horizon credit before the deterministic row work. -/
theorem twp_round_prefix (E : CoPset) (a : Coefficients) (r : a.Realization)
    (p : unitInterval) (self coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a r bounds) (hnext : NextSpec (GF := GF) E a next)
    (l : Loc) (F : Bool → ℝ≥0∞) (N t : ℕ) (x : a.State t) (q : List Bool)
    (lo hi : Fraction) (Φ : Val rT → IProp GF)
    (hfinish : ∀ d : a.Branch t,
      iprop(UniformBag.owns l q ∗ ↯ (a.credit p F N (t + 1) (a.advance t x d) q)) ⊢
        tglWp E (Program.afterConditional self l (a.degree (t + 1)) (a.advance t x d).1
          lo hi
          (r.raw (t + 1) (a.advance t x d).1 false)
          (r.raw (t + 1) (a.advance t x d).1 true)
          (.ofRat (a.lowerBarQ t (a.advance t x d).1))
          (.ofRat (a.upperBarQ t (a.advance t x d).1))) Φ) :
    iprop(UniformBag.owns l q ∗ ↯ (a.credit p F (N + 1) t x q)) ⊢
      tglWp E (roundWithSelf self coin bounds next l (a.degree t) x.1
        lo hi) Φ := by
  unfold roundWithSelf Program.roundCode Program.afterConditionalCode Program.afterRescaleCode
  simp only [conditionalBody_explicit]
  unfold EnvelopeConditionalAverage.loopCode
  iintro ⟨Hbag, Hcredit⟩
  twp_bind pl(&next.fst #int (a.degree t : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hnext t
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  rw [degree_test a t]
  iterate 2 twp_pure
  rw [← Nat.cast_sub (a.grows t).le]
  simp only [ClosedExp.openRec]
  twp_bind pl(&Occil.binomial &coin.fst #int ((a.degree (t + 1) - a.degree t : ℕ) : ℤ))
  isimp only [← a.expectation p F N t x q] at Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply BinomialFinite.twp_binomial E p coin hcoin (a.degree (t + 1) - a.degree t)
      (fun d => a.credit p F N (t + 1) (a.advance t x d) q) $$ Hcredit
  iintro %v ⟨%d, %hv, Hcredit⟩
  subst v
  isimp only [BinomialFinite.encode, Exp.ofVal]
  twp_bind pl(#int ((x.1 : ℕ) : ℤ) + #int ((d : ℕ) : ℤ))
  twp_pure
  twp_value
  imodintro
  rw [← Nat.cast_add]
  twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&bounds.fst #int (a.degree (t + 1) : ℤ)
    #int (((a.advance t x d).1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hbounds (t + 1) (by omega) (a.advance t x d).1
  iintro %v %hv
  subst v
  iterate 6 twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&(EnvelopeConditionalAverage.conditionalClosure bounds
    (a.degree t) (a.degree (t + 1)) (a.advance t x d).1).fst #false)
  iapply tglWp_wand
  isplitl []
  · have h := twp_conditional E a r bounds hbounds t (a.advance t x d).1 false
    simp only [Bool.false_eq_true, ite_false] at h
    iapply h
  iintro %v %hv
  subst v
  twp_pure
  simp only [ClosedExp.openRec]
  twp_bind pl(&(EnvelopeConditionalAverage.conditionalClosure bounds
    (a.degree t) (a.degree (t + 1)) (a.advance t x d).1).fst #true)
  iapply tglWp_wand
  isplitl []
  · have h := twp_conditional E a r bounds hbounds t (a.advance t x d).1 true
    simp only [ite_true] at h
    iapply h
  iintro %v %hv
  subst v
  twp_pure
  simp only [ClosedExp.openRec]
  simp only [← Fraction.encode_ofRat]
  ieval (
    change _ ⊢ tglWp E (Program.afterConditional self l (a.degree (t + 1))
      (a.advance t x d).1 lo hi
      (r.raw (t + 1) (a.advance t x d).1 false)
      (r.raw (t + 1) (a.advance t x d).1 true)
      (.ofRat (a.lowerBarQ t (a.advance t x d).1))
      (.ofRat (a.upperBarQ t (a.advance t x d).1))) Φ)
  iapply hfinish d
  iframe Hbag Hcredit

end specification

end

end SampLib.EnvelopeFactory
