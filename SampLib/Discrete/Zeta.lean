import SampLib.Discrete.Laws.Zeta
import SampLib.Discrete.Support.ZetaSyntax
import SampLib.Uniform.FairCoin
import SampLib.Bernoulli.Complement
import SampLib.Core.Syntax.ClosedExp

/-! # Exact zeta rejection from dyadic blocks

A complemented power coin chooses geometric levels. Independent uniform ranks
and reciprocal-power acceptance leave the canonical positive zeta law.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.Zeta

noncomputable section

open DyadicBlocks

private def fairCall {rT : Type _} : Val rT :=
  ⟨pl(fun u, &Occil.fairCoin #()), .lam (by is_lc), by is_lc⟩

private def proposalCoin {rT : Type _} (a b : ℕ) : Val rT :=
  ⟨pl(fun u, ~(&Occil.DiscreteExtra.rationalPowerCoin &(fairCall (rT := rT)).fst
    (#int (a : ℤ) - #int (b : ℤ)) #int (b : ℤ) #())), .lam (by is_lc), by is_lc⟩

private instance proposal_closed {rT : Type _} (a b : ℕ) :
    ClosedExp ((proposalCoin a b : Val rT).fst) where
  lc := by is_lc
  fv := by simp [proposalCoin, fairCall, Exp.fv, RationalPowerCoinSyntax.fv, FairCoin.fairCoin_fv]

private def ratioCoin {rT : Type _} (t : Block) : Val rT :=
  ⟨pl(fun u, &Occil.rationalCoin #int (2 ^ t.1 : ℕ) #int (value t)),
    .lam (by is_lc), by is_lc⟩

private theorem ratio_bias (t : Block) :
    RationalCoin.bias (2 ^ t.1 : ℕ) (value t) (by positivity)
      (by exact_mod_cast value_pos t) (by unfold value; omega) = ratio t := by
  apply Subtype.ext
  simp [RationalCoin.bias, ratio]

private theorem difference_cast (a b : ℕ) (hab : b < a) :
    (a : ℤ) - b = ((a - b : ℕ) : ℤ) := (Nat.cast_sub hab.le).symm

private theorem power_cast (l : ℕ) : (2 : ℤ) ^ l = ((2 ^ l : ℕ) : ℤ) := by norm_cast

private theorem bool_not (s : Bool) : Bool.rec true false s = !s := by cases s <;> rfl

private theorem proposal_moment (a b : ℕ) (hb : 0 < b) (F : Bool → ℝ≥0∞) :
    (∫⁻ s, F (!s) ∂RealCoin.law (RationalPower.bias VonNeumann.fairBias (a - b) b hb)) =
      ∫⁻ s, F s ∂RealCoin.law (bias a b hb) :=
  Complement.expectation_preservation (tail a b hb) F

private def loop {rT : Type _} (a b : ℕ) : Exp rT := pl%
  rec draw u :=
    let level := &Occil.geometric &(proposalCoin a b).fst #();
    let start := &Occil.DiscreteExtra.integerPower #2 level;
    let value := start + &Occil.uniformInt start;
    if &Occil.DiscreteExtra.rationalPowerCoin (fun u, &Occil.rationalCoin start value)
        #int (a : ℤ) #int (b : ℤ) #() then value else draw #()

private theorem valid_test (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    Bool.or (decide ((b : ℤ) ≤ 0)) (decide ((a : ℤ) ≤ b)) = false := by
  simp [hb.ne', not_le.mpr hab]

attribute [local pl_step_simp]
  ZetaSyntax.geometric_openRec ZetaSyntax.geometric_closeRec
  ZetaSyntax.power_openRec ZetaSyntax.power_closeRec
  RationalPowerCoinSyntax.openRec RationalPowerCoinSyntax.closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec
  UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec
  FairCoin.fairCoin_openRec FairCoin.fairCoin_closeRec

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem fairCall_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(fairCall (rT := rT)).fst #())
      (RealCoin.law VonNeumann.fairBias) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (FairCoin.fairCoin_distSpec E).spec F hF $$ Hcredit

private theorem proposalCoin_spec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    IsDistSpec (GF := GF) E pl(&(proposalCoin a b).fst #())
      (RealCoin.law (bias a b hb)) Val.bool := by
  have hpower := RationalPower.rationalPowerCoin_distSpec (rT := rT) (GF := GF)
    E VonNeumann.fairBias (a - b) b hb
    (fairCall (rT := rT)) (fairCall_spec E)
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  iterate 2 twp_pure
  rw [difference_cast a b hab]
  twp_bind pl(&Occil.DiscreteExtra.rationalPowerCoin &(fairCall (rT := rT)).fst
    #int (a - b : ℕ) #int (b : ℤ) #())
  isimp only [← proposal_moment a b hb F] at Hcredit
  iapply hpower.wp (fun s => F (!s)) (measurable_of_countable _) _ $$ Hcredit
  iintro %s Hcredit
  twp_pure
  twp_value
  imodintro
  iexists !s
  iframe Hcredit
  ipureintro
  simp only [Val.ext_iff, bool_not]

private theorem ratioCoin_spec (E : CoPset) (t : Block) :
    IsDistSpec (GF := GF) E pl(&(ratioCoin t).fst #()) (RealCoin.law (ratio t)) Val.bool := by
  have h := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF) E
    (2 ^ t.1 : ℕ) (value t) (by positivity) (by exact_mod_cast value_pos t)
      (by unfold value; omega)
  rw [ratio_bias] at h
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  twp_pure
  iapply h.spec F hF $$ Hcredit

private theorem acceptance_spec (E : CoPset) (a b : ℕ) (hb : 0 < b) (t : Block) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.rationalPowerCoin &(ratioCoin t).fst
        #int (a : ℤ) #int (b : ℤ) #()) (RealCoin.law (acceptance a b hb t)) Val.bool :=
  RationalPower.rationalPowerCoin_distSpec E (ratio t) a b hb (ratioCoin t) (ratioCoin_spec E t)

omit [ProbLangDist.IsUniformInt rT] in
private abbrev loop_align (E : CoPset) (a b : ℕ) (Φ : Val rT → IProp GF) := by
  have h : tglWp (rT := rT) (GF := GF) E pl(&(loop a b) #()) Φ ⊢
      tglWp E pl(&(loop a b) #()) Φ := BI.BIBase.Entails.refl _
  conv at h =>
    rhs
    simp [loop, Exp.close, Exp.closeRec, ClosedExp.closeRec]
  exact h

omit [ProbLangDist.IsUniformInt rT] in
private abbrev source_align (E : CoPset) (a b : ℕ) (Φ : Val rT → IProp GF) := by
  have h := loop_align (rT := rT) (GF := GF) E a b Φ
  conv at h =>
    rhs
    simp [proposalCoin, fairCall, Exp.close, Exp.closeRec]
  exact h

private theorem twp_loop (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ n, F n ∂law a b hb hab) -∗
      tglWp E pl(&(loop a b) #())
        (fun v : Val rT => iprop(∃ (n : ℕ), ⌜v = Val.int n⌝ ∗ ↯ (F n))) := by
  have hgeo := Geometric.geometric_distSpec (rT := rT) (GF := GF) E (bias a b hb)
    (bias_pos a b hb hab) (proposalCoin a b) (proposalCoin_spec E a b hb hab)
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor a b hb hab) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.geometric &(proposalCoin a b).fst #())
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation a b hb hab F ε) $$ Htotal
  iapply hgeo.wp (levelCredit a b hb hab F ε) (measurable_of_countable _) _ $$ Hsample
  iintro %l Hcredit
  isimp only [levelCredit] at Hcredit
  twp_pure
  twp_bind pl(&Occil.DiscreteExtra.integerPower #2 #int (l : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply twp_integerPower E 2 l
  iintro %v %hv
  subst v
  rw [power_cast]
  twp_pure
  have : NeZero (2 ^ l) := ⟨by positivity⟩
  twp_bind pl(&Occil.uniformInt #int (2 ^ l : ℕ))
  iapply (UniformFin.uniformFin_distSpec E (2 ^ l)).wp
    (fun r => proposalCredit a b hb hab F ε ⟨l, r⟩) (measurable_of_countable _) _ $$ Hcredit
  iintro %r Hcredit
  twp_pure
  rw [← Nat.cast_add]
  twp_pure
  twp_bind pl(&Occil.DiscreteExtra.rationalPowerCoin &(ratioCoin ⟨l, r⟩).fst
    #int (a : ℤ) #int (b : ℤ) #())
  isimp only [proposalCredit] at Hcredit
  iapply (acceptance_spec E a b hb ⟨l, r⟩).wp (coinCredit a b hb hab F ε ⟨l, r⟩)
    (measurable_of_countable _) _ $$ Hcredit
  iintro %accepted Hcredit
  cases accepted
  · twp_pure
    isimp only [coinCredit, Bool.false_eq_true, ↓reduceIte] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    iapply loop_align E a b
      (fun v : Val rT => iprop(∃ (n : ℕ), ⌜v = Val.int n⌝ ∗ ↯ (F n)))
    iapply IH $$ Hterm Hcredit
  · twp_pure
    twp_value
    imodintro
    iexists value ⟨l, r⟩
    isimp only [coinCredit, ↓reduceIte] at Hcredit
    iframe Hcredit
    ipureintro
    rfl

/-- Exact zeta on the positive naturals for every rational exponent greater than one. -/
theorem zeta_distSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.zeta #int (a : ℤ) #int (b : ℤ))
      (law a b hb hab) (fun n => Val.int (n : ℤ)) where
  spec F _ := by
    iintro Hcredit
    iterate 5 twp_pure
    rw [valid_test a b hb hab]
    iterate 3 twp_pure
    iapply source_align E a b
      (fun v : Val rT => iprop(∃ (n : ℕ), ⌜v = Val.int n⌝ ∗ ↯ (F n)))
    iapply twp_loop E a b hb hab F $$ Hcredit

end specification

end

end SampLib.Zeta
