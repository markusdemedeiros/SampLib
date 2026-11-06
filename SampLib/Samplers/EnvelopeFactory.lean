import SampLib.EnvelopeRound
import SampLib.EnvelopeStateStep
import SampLib.EnvelopeCompare

/-! # The general reverse-time Bernstein-envelope factory

Finite horizon induction uses one joint history/uniform continuation credit.
The analytic limit identifies its initial cost; the program proof only advances
the row, rescales exact fractions, and observes the same owned uniform.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.EnvelopeFactory

open FactoryFractions

noncomputable section

private theorem call_as_value {rT : Type} (coin bounds next : Val rT) (l : Loc)
    (n heads : ℕ) (lo hi : Fraction) :
    Program.call coin bounds next l n heads lo hi =
      pl(&(Program.loopValue coin bounds next l).fst #int (n : ℤ) #int (heads : ℤ)
        &lo.encode.fst &hi.encode.fst) := rfl

private theorem initial_call {rT : Type} (a : Coefficients) (coin bounds next : Val rT) (l : Loc) :
    Program.call coin bounds next l (a.degree 0) a.initial.1
      (a.stateLower 0 a.initial) (a.stateUpper 0 a.initial) =
        Program.call coin bounds next l 0 0 (.ofRat 0) (.ofRat 1) := by
  change Program.call coin bounds next l (a.degree 0) 0 (.ofRat 0) (.ofRat 1) = _
  rw [a.initial_degree]

private def consecutive {rT : Type} : Val rT :=
  ⟨.lam (.binop .plus (.bvar 0) pl(#1)), .lam (by is_lc), by is_lc⟩

private instance envelope_closed {rT : Type} :
    ClosedExp (Occil.FactoryExtra.envelopeFactoryDegrees : Exp rT) where
  lc := by rw [Program.source_eq]; exact Program.source_lc
  fv := by
    simp [Occil.FactoryExtra.envelopeFactoryDegrees, Exp.fv, ClosedExp.closeRec, ClosedExp.fv,
      Occil.newUniformBag]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local irreducible] FactoryFractions.encode FactoryFractions.Fraction.encode

private theorem twp_until (E : CoPset) (a : Coefficients) (r : a.Realization)
    (p : unitInterval) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a r bounds) (hnext : NextSpec (GF := GF) E a next)
    (l : Loc) (F : Bool → ℝ≥0∞) (N t : ℕ) (x : a.State t)
    (hx : 0 < a.toScheme.weight t x.1 x.2) (q : List Bool)
    (hlo : DyadicPosterior.resolves q ((a.process p).lower t x) false)
    (hhi : DyadicPosterior.resolves q ((a.process p).upper t x) true) :
    iprop(UniformBag.owns l q ∗ ↯ (a.credit p F N t x q)) ⊢
      tglWp E (Program.call coin bounds next l (a.degree t) x.1
        (a.stateLower t x) (a.stateUpper t x))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction N generalizing t x q with
  | zero =>
    iintro ⟨Hbag, Hcredit⟩
    iexfalso
    iapply ErrorCredit.contradict (a.unresolved_credit p F t x q hlo hhi) $$ Hcredit
  | succ N IH =>
    iintro Hstate
    iapply Program.twp_open_round E coin bounds next l (a.degree t) x.1
      (a.stateLower t x) (a.stateUpper t x) _
    rw [round_eq_withSelf]
    iapply twp_round_prefix E a r p (Program.loopValue coin bounds next l) coin bounds next
      hcoin hbounds hnext l F N t x q (a.stateLower t x) (a.stateUpper t x) _ ?_
    · intro d
      iintro Hnext
      iapply twp_rescale E (Program.loopValue coin bounds next l) l (a.degree (t + 1))
        (a.advance t x d).1 (a.stateLower t x) (a.stateUpper t x)
        (r.raw (t + 1) (a.advance t x d).1 false)
        (r.raw (t + 1) (a.advance t x d).1 true)
        (.ofRat (a.lowerBarQ t (a.advance t x d).1))
        (.ofRat (a.upperBarQ t (a.advance t x d).1))
        (by simpa only [Fraction.value_ofRat] using a.oldWidth_positive p t x d q hx hlo hhi) _
      rw [(r.rescaled_state t x d).1, (r.rescaled_state t x d).2]
      iapply twp_compare E a p F N (t + 1) (a.advance t x d)
        (Program.loopValue coin bounds next l) l
        (a.stateLower (t + 1) (a.advance t x d)) (a.stateUpper (t + 1) (a.advance t x d))
        (a.stateLower_coe p (t + 1) (a.advance t x d))
        (a.stateUpper_coe p (t + 1) (a.advance t x d)) ?_ q
      · intro s hlo' hhi'
        have hc := IH (t + 1) (a.advance t x d) (a.advance_positive t x d hx) s hlo' hhi'
        simpa only [call_as_value] using hc
      · iexact Hnext
    · iexact Hstate

/-- The actual adaptive-degree source, with arbitrary raw coefficient and coin callbacks. -/
theorem twp_envelopeFactoryDegrees (E : CoPset) (p : unitInterval) (a : Parameters p)
    (r : a.toCoefficients.Realization) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit a.target F) -∗
      tglWp E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
        &coin.fst &bounds.fst &next.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := a.exists_credit_horizon F δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  iapply Program.twp_open_initialization E coin bounds next _
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  isimp only [Exp.ofVal]
  iapply Program.twp_open_bag E coin bounds next l _
  have ht := twp_until E a.toCoefficients r p coin bounds next hcoin hbounds hnext l F N 0
    a.toCoefficients.initial (by exact zero_lt_one) []
    (DyadicPosterior.resolves_false [] le_rfl) (DyadicPosterior.resolves_true [] le_rfl)
  rw [initial_call] at ht
  iapply ht
  iframe Hbag Hcredit

/-- Strictly increasing deterministic degrees and consistent rational envelopes whose
Bernstein means converge at the input bias. -/
theorem envelopeFactoryDegrees_distSpec (E : CoPset) (p : unitInterval) (a : Parameters p)
    (r : a.toCoefficients.Realization) (coin bounds next : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds)
    (hnext : NextSpec (GF := GF) E a.toCoefficients next) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactoryDegrees
      &coin.fst &bounds.fst &next.fst #()) (RealCoin.law a.target) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using wand_entails
      (twp_envelopeFactoryDegrees E p a r coin bounds next hcoin hbounds hnext F)

omit [ProbLangDist.IsUniformInt rT] in
private theorem consecutive_spec (E : CoPset) (a : Coefficients) (ha : ∀ t, a.degree t = t) :
    NextSpec (GF := GF) E a (consecutive : Val rT) := by
  intro t
  rw [ha t, ha (t + 1)]
  twp_pures
  twp_value
  imodintro
  ipureintro
  simp only [Nat.cast_add, Nat.cast_one]

/-- The original consecutive-degree wrapper, under the same complete coefficient contract. -/
theorem envelopeFactory_distSpec (E : CoPset) (p : unitInterval) (a : Parameters p)
    (r : a.toCoefficients.Realization) (ha : ∀ t, a.degree t = t) (coin bounds : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hbounds : BoundsSpec (GF := GF) E a.toCoefficients r bounds) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.envelopeFactory &coin.fst &bounds.fst #())
      (RealCoin.law a.target) Val.bool where
  spec F hF := by
    have hs := (envelopeFactoryDegrees_distSpec E p a r coin bounds consecutive hcoin hbounds
      (consecutive_spec E a.toCoefficients ha)).spec F hF
    simp only [consecutive] at hs
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    iapply hs $$ Hcredit

end specification

end

end SampLib.EnvelopeFactory
