import SampLib.Constants.Laws.PositiveSeries
import SampLib.Bernoulli.Support.UniformBagChoice
import SampLib.Core.BetaStep
import SampLib.Constants.Syntax.PositiveSeries

/-! # Exact sampling from a positive rational series

The accumulator represents the prefix sum exactly. The current term's certified
remainder brackets the canonical sum. A fixed uncertainty horizon then supplies
the same finite-induction credit argument as rational enclosures.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FromPositiveSeries

open Program

noncomputable section

/-- The source tuple `(a,(b,(errorNumerator,errorDenominator)))`. -/
def encodeCoefficient {rT : Type} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.numerator) (Val.pair (Val.int c.denominator)
    (Val.pair (Val.int c.errorNumerator) (Val.int c.errorDenominator)))

private theorem valid_guard (c : Coefficient) :
    (decide ((c.denominator : ℤ) ≤ 0) || decide ((c.errorDenominator : ℤ) ≤ 0)) = false := by
  simp [c.positive.ne', c.errorPositive.ne']

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_round (E : CoPset) (a : Parameters) (term : Val rT)
    (hterm : ∀ n : ℕ, ⊢ tglWp E pl(&term.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeCoefficient (a.coefficient n)⌝)))
    (l : Loc) (N n : ℕ) (F : Bool → ℝ≥0∞)
    (hcontinue : ∀ q : List Bool,
      DyadicPosterior.resolves q (enclosure a n).left false →
      DyadicPosterior.resolves q (enclosure a n).right true →
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q
        (FromBounds.horizonCredit (enclosure a N) F))) ⊢
        tglWp E pl(&(loop term l) #int ((n + 1 : ℕ) : ℤ)
          #int ((accumulator a (n + 1)).numerator : ℤ)
          #int ((accumulator a (n + 1)).denominator : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q
      (FromBounds.horizonCredit (enclosure a N) F))) ⊢
      tglWp E pl(&(loop term l) #int (n : ℤ)
        #int ((accumulator a n).numerator : ℤ) #int ((accumulator a n).denominator : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro ⟨Hbag, Hcredit⟩
  iterate 4 (
    twp_pure
    simp -failIfUnchanged only [UniformBag.uniformBagLess_openRec])
  twp_bind pl(&term.fst #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hterm n
  iintro %v %hv
  subst v
  twp_pures
  simp only [Bool.or_assoc, Bool.false_or, valid_guard]
  iterate 7 twp_pure
  rw [numerator_step a n, denominator_step a n]
  simp only [UniformBag.uniformBagLess_openRec]
  ieval (
    change _ ⊢ tglWp E
      (UniformBag.choice l ((accumulator a (n + 1)).numerator : ℤ)
        ((accumulator a (n + 1)).denominator : ℤ) pl(#true) _) _)
  iapply UniformBag.twp_choice E l q _ _ (lower_denominator_pos a n)
    (FromBounds.horizonCredit (enclosure a N) F)
    (FromBounds.measurable_horizonCredit (enclosure a N) F) pl(#true) _ _ ?_ ?_
  · intro r _ hlo
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists true
    ihave Hcredit := ErrorCredit.weaken
      (FromBounds.lower_credit (enclosure a n) (enclosure a N) r F
        (lower_resolves a n hlo)) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r _ hlo
    iintro ⟨Hbag, Hcredit⟩
    iterate 6 twp_pure
    rw [upper_numerator_step a n, upper_denominator_step a n]
    simp only [UniformBag.uniformBagLess_openRec]
    ieval (
      change _ ⊢ tglWp E
        (UniformBag.choice l (enclosure a n).upper ((enclosure a n).denominator : ℤ)
          _ pl(#false)) _)
    iapply UniformBag.twp_choice E l r _ _ (upper_denominator_pos a n)
      (FromBounds.horizonCredit (enclosure a N) F)
      (FromBounds.measurable_horizonCredit (enclosure a N) F) _ pl(#false) _ ?_ ?_
    · intro s hs hhi
      iintro ⟨Hbag, Hcredit⟩
      twp_pure
      rw [← Nat.cast_add_one]
      ieval (
        change _ ⊢ tglWp E pl(&(loop term l) #int ((n + 1 : ℕ) : ℤ)
          #int ((accumulator a (n + 1)).numerator : ℤ)
          #int ((accumulator a (n + 1)).denominator : ℤ)) _)
      iapply hcontinue s (lower_resolves a n (DyadicPosterior.resolves_refines hs hlo))
        (upper_resolves a n hhi)
      iframe Hbag Hcredit
    · intro s _ hhi
      iintro ⟨Hbag, Hcredit⟩
      twp_value
      imodintro
      iexists false
      ihave Hcredit := ErrorCredit.weaken
        (FromBounds.upper_credit (enclosure a n) (enclosure a N) s F
          (upper_resolves a n hhi)) $$ Hcredit
      iframe Hcredit
      itrivial
    · iframe Hbag Hcredit
  · iframe Hbag Hcredit

private theorem twp_until (E : CoPset) (a : Parameters) (term : Val rT)
    (hterm : ∀ n : ℕ, ⊢ tglWp E pl(&term.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeCoefficient (a.coefficient n)⌝)))
    (l : Loc) (N n : ℕ) (hn : n ≤ N) (F : Bool → ℝ≥0∞) (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q
      (FromBounds.horizonCredit (enclosure a N) F))) ⊢
      tglWp E pl(&(loop term l) #int (n : ℤ)
        #int ((accumulator a n).numerator : ℤ) #int ((accumulator a n).denominator : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hall : ∀ n ≤ N, ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q
        (FromBounds.horizonCredit (enclosure a N) F))) ⊢
        tglWp E pl(&(loop term l) #int (n : ℤ)
          #int ((accumulator a n).numerator : ℤ) #int ((accumulator a n).denominator : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q
        (FromBounds.horizonCredit (enclosure a N) F))) ⊢
        tglWp E pl(&(loop term l) #int (n : ℤ)
          #int ((accumulator a n).numerator : ℤ) #int ((accumulator a n).denominator : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) ?_ ?_ hn
    · intro n hn IH q
      iapply twp_round E a term hterm l N n F (fun q _ _ => IH q) q
    · intro q
      iapply twp_round E a term hterm l N N F ?_ q
      intro q hlo hhi
      iintro ⟨Hbag, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict
        (FromBounds.unresolved_credit (enclosure a N) q F hlo hhi) $$ Hcredit
  exact hall n hn q

/-- The exact source accumulator and its canonical sum share one latent uniform. -/
theorem twp_fromPositiveSeries (E : CoPset) (a : Parameters) (term : Val rT)
    (hterm : ∀ n : ℕ, ⊢ tglWp E pl(&term.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeCoefficient (a.coefficient n)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias a) F) -∗
      tglWp E pl(&Occil.Constants.fromPositiveSeries &term.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  rw [source_eq]
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := FromBounds.exists_horizon (enclosure a) (enclosures_tight a) F δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([EctxItem.appL Val.unit] : Ectx rT) (.app (.lam sourceBody) term.fst)) _)
  iapply (twp_beta E [.appL Val.unit] sourceBody term source_locallyClosed _)
  ieval (change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT) (.app (.lam _) Val.unit.fst)) _)
  iapply (twp_beta E [] _ Val.unit (unit_locallyClosed term) _)
  simp only [Exp.open', Exp.openRec, Occil.newUniformBag,
    Nat.reduceAdd, Nat.reduceEqDiff]
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  rw [inserted_callback]
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (.app (.lam (bagBody term)) (Val.loc l).fst)) _)
  iapply (twp_beta E [] (bagBody term) (Val.loc l) (bag_locallyClosed term) _)
  ieval (
    change _ ⊢ tglWp E ((bagBody term).open' (Val.loc l).fst) _)
  rw [opened_bag]
  have hloopLC := loop_locallyClosed term l
  let loopVal : Val rT := ⟨loop term l, .fix hloopLC, hloopLC⟩
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (.app (.lam pl(⟪bvar 0⟫ #0 #0 #1)) loopVal.fst)) _)
  iapply (twp_beta E [] pl(⟪bvar 0⟫ #0 #0 #1) loopVal (by is_lc) _)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec, loopVal, ↓reduceIte]
  have hloop := twp_until (rT := rT) (GF := GF) E a term hterm l N 0 (Nat.zero_le _) F []
  simp only [accumulator] at hloop
  iapply hloop
  iframe Hbag Hcredit

/-- Bernoulli at the normalized ordinary sum, with arbitrary certified tight tail bounds. -/
theorem fromPositiveSeries_distSpec (E : CoPset) (a : Parameters) (term : Val rT)
    (hterm : ∀ n : ℕ, ⊢ tglWp E pl(&term.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeCoefficient (a.coefficient n)⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.fromPositiveSeries &term.fst #())
      (RealCoin.law (bias a)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_fromPositiveSeries E a term hterm F)

end specification

end

end SampLib.FromPositiveSeries
