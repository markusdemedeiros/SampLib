import SampLib.Discrete.Laws.DiscreteLaplaceCredits
import SampLib.Uniform.FairCoin
import SampLib.Core.Syntax.ClosedExp
import Samplers.Discrete.Tails

/-! # Exact discrete Laplace from a rational positive rate

One rejection budget covers both a failed exponential test and negative zero.
The analytic lattice argument identifies the accepted signed quotient law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.DiscreteLaplace

noncomputable section

private def wholeCoin {rT : Type _} : Val rT :=
  ⟨pl(fun u, &Occil.expMinusRational #1 #1 #()), .lam (by is_lc), by is_lc⟩

private def loop {rT : Type _} (s t : ℕ) : Exp rT := pl%
  rec draw u :=
    let remainder := &Occil.uniformInt #int (t : ℤ);
    if &Occil.expMinusRational remainder #int (t : ℤ) #() then
      let whole := &Occil.geometricFailures &(wholeCoin (rT := rT)).fst #0;
      let magnitude := (remainder + whole * #int (t : ℤ)) / #int (s : ℤ);
      if &Occil.fairCoin #() then magnitude else
        if magnitude = #0 then draw #() else -magnitude
    else draw #()

private instance geometricFailures_closed {rT : Type _} :
    ClosedExp (Occil.geometricFailures : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.geometricFailures, Exp.fv]

private instance wholeCoin_closed {rT : Type _} : ClosedExp (wholeCoin (rT := rT)).fst where
  lc := wholeCoin.lc
  fv := by simp [wholeCoin, Exp.fv, ExpMinusRational.expMinusRational_fv]

attribute [local simp] ClosedExp.openRec ClosedExp.closeRec

private theorem loop_lc {rT : Type _} (s t : ℕ) : (loop (rT := rT) s t).IsLocallyClosed := by
  unfold loop
  is_lc

private theorem magnitude_cast (s t r w : ℕ) :
    ((r : ℤ) + (w : ℤ) * t) / s = (magnitude s t (r, (w, false)) : ℤ) := by
  simp [magnitude, Nat.cast_add, Nat.cast_mul, Int.natCast_ediv]

private theorem positive_test (n : ℕ) (hn : 0 < n) :
    decide ((n : ℤ) ≤ 0) = false := by simp [Nat.ne_of_gt hn]

private theorem zero_test {rT : Type _} [BEq rT] (n : ℕ) (hn : n ≠ 0) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = false := by
  change ((n : ℤ) == 0) = false
  apply beq_eq_false_iff_ne.mpr
  exact_mod_cast hn

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec
  ExpMinusRational.expMinusRational_openRec ExpMinusRational.expMinusRational_closeRec
  FairCoin.fairCoin_openRec FairCoin.fairCoin_closeRec ClosedExp.openRec ClosedExp.closeRec

private theorem wholeCoin_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(wholeCoin (rT := rT)).fst #())
      (RealCoin.law wholeBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    isimp only [wholeBias] at Hcredit
    iapply ((ExpMinusRational.expMinusRational_distSpec (rT := rT) (GF := GF)
      E 1 1 zero_le_one zero_lt_one).wp
      F hF _) $$ Hcredit
    iintro %b Hcredit
    iexists b
    iframe Hcredit
    ipureintro
    rfl

private theorem twp_loop (E : CoPset) (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (credit s t hs ht F) -∗ tglWp E pl(&(loop s t) #())
      (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  have hlooplc := loop_lc (rT := rT) s t
  have hgeom := GeometricFailures.geometricFailures_distSpec (rT := rT) (GF := GF) E
    wholeBias whole_lt_one wholeCoin (wholeCoin_distSpec E) 0
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor s t ht) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pure
  twp_pure
  twp_bind pl(&Occil.uniformInt #int (t : ℤ))
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken (expectation_preservation s t hs ht F ε) $$ Htotal
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E t ht (rankCredit s t hs ht F ε)) $$ Hcredit
  iintro %v ⟨%r, %hv, %hr, Hcredit⟩
  subst v
  twp_pure
  twp_bind pl(&Occil.expMinusRational #int (r : ℤ) #int (t : ℤ) #())
  isimp only [rankCredit] at Hcredit
  iapply ((ExpMinusRational.expMinusRational_distSpec E r t
    (Int.natCast_nonneg r) (Int.natCast_pos.mpr ht)).wp
    (expCredit s t hs ht F ε r) (measurable_of_countable _) _) $$ Hcredit
  iintro %accepted Hcredit
  cases accepted with
  | false =>
    twp_pure
    isimp only [expCredit, Bool.false_eq_true, ite_false, retryCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    isimp [loop, Exp.close, Exp.closeRec] at IH
    iapply IH $$ Hterm Hcredit
  | true =>
    twp_pure
    twp_bind pl(&Occil.geometricFailures &(wholeCoin (rT := rT)).fst #0)
    isimp only [expCredit, ite_true] at Hcredit
    iapply (hgeom.wp (wholeCredit s t hs ht F ε r) (measurable_of_countable _) _) $$ Hcredit
    iintro %w Hcredit
    simp only [zero_add]
    iterate 4 twp_pure
    rw [magnitude_cast]
    twp_pure
    twp_bind pl(&Occil.fairCoin #())
    isimp only [wholeCredit] at Hcredit
    iapply ((FairCoin.fairCoin_distSpec E).wp (signCredit s t hs ht F ε r w)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b with
    | false =>
      twp_pure
      by_cases hm : magnitude s t (r, (w, false)) = 0
      · rw [hm]
        iterate 2 twp_pure
        isimp only [signCredit, hm, _root_.and_self, ite_true, retryCredit] at Hcredit
        ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
        isimp [loop, Exp.close, Exp.closeRec] at IH
        iapply IH $$ Hterm Hcredit
      · twp_pure
        rw [zero_test _ hm]
        twp_pure
        twp_pure
        twp_value
        imodintro
        iexists output s t (r, (w, false))
        isimp only [signCredit, hm, _root_.and_false, ite_false] at Hcredit
        iframe Hcredit
        ipureintro
        rfl
    | true =>
      twp_pure
      twp_value
      imodintro
      iexists output s t (r, (w, true))
      isimp only [signCredit, Bool.true_eq_false, _root_.false_and, ite_false] at Hcredit
      iframe Hcredit
      ipureintro
      rfl

/-- The full positive-rational-rate domain has the canonical discrete-Laplace law. -/
theorem twp_discreteLaplace (E : CoPset) (s t : ℕ) (hs : 0 < s) (ht : 0 < t)
    (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ z, F z ∂law s t hs ht) -∗
      tglWp E pl(&Occil.DiscreteExtra.discreteLaplace #int (s : ℤ) #int (t : ℤ))
        (fun v : Val rT => iprop(∃ z : ℤ, ⌜v = Val.int z⌝ ∗ ↯ (F z))) := by
  have hloop := twp_loop (rT := rT) (GF := GF) E s t hs ht F
  simp [loop, wholeCoin, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  isimp [Occil.DiscreteExtra.discreteLaplace, Exp.close, Exp.closeRec]
  twp_pures
  simp only [positive_test s hs, positive_test t ht, Bool.or_false]
  iterate 2 twp_pure
  exact wand_entails hloop

theorem discreteLaplace_distSpec (E : CoPset) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.discreteLaplace #int (s : ℤ) #int (t : ℤ))
      (law s t hs ht) Val.int where
  spec F _ := wand_entails (twp_discreteLaplace E s t hs ht F)

end specification

end

end SampLib.DiscreteLaplace
