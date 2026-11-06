import SampLib.Distributions.AlternatingSeriesState
import SampLib.Syntax.AlternatingSeries
import SampLib.BetaStep

/-! # The arbitrary alternating-series Bernoulli factory

One live input-coin product selects an independent stopping threshold. Both
rational comparisons refine the posterior of the same cached uniform value.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AlternatingSeries

open FactoryFractions Program

noncomputable section

private def fractionChoice {rT : Type} (l : Loc) (a : Fraction)
    (yes no : Exp rT) : Exp rT :=
  .cond pl(&Occil.uniformBagLess #loc l (fst(&a.encode.fst)) (snd(&a.encode.fst))) yes no

private def prepared {rT : Type} (self : Val rT) (l : Loc) (n : ℕ)
    (lo hi : Fraction) (b : Bool) : Exp rT :=
  let retry := pl(&self.fst (#int ((n + 1 : ℕ) : ℤ) + #1)
    &lo.encode.fst &hi.encode.fst #bool b)
  fractionChoice l lo pl(#true) (fractionChoice l hi retry pl(#false))

private def afterTerm {rT : Type} (self : Val rT) (l : Loc) (n : ℕ)
    (lo hi c : Fraction) (b : Bool) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess pl(#loc l)) (.fst x)) (.snd x)
  let retry := pl(&self.fst (#int ((n + 1 : ℕ) : ℤ) + #1)
    {Exp.bvar 1} {Exp.bvar 0} #bool b)
  let branch := .cond (compare (.bvar 1)) pl(#true)
    (.cond (compare (.bvar 0)) retry pl(#false))
  let upper := .cond pl(#int ((n + 1 : ℕ) : ℤ) % #2 = #0)
    (.app (.app Occil.FactoryExtra.addFraction lo.encode.fst) c.encode.fst) hi.encode.fst
  let lower := .cond pl(#int ((n + 1 : ℕ) : ℤ) % #2 = #1)
    (.app (.app Occil.FactoryExtra.subtractFraction hi.encode.fst) c.encode.fst) lo.encode.fst
  bind lower (bind upper branch)

private def afterCoin {rT : Type} (self coefficient : Val rT) (l : Loc) (n : ℕ)
    (lo hi : Fraction) (b : Bool) : Exp rT :=
  let bind (rhs body : Exp rT) := .app (.lam body) rhs
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess pl(#loc l)) (.fst x)) (.snd x)
  let retry := pl(&self.fst (#int ((n + 1 : ℕ) : ℤ) + #1)
    {Exp.bvar 1} {Exp.bvar 0} #bool b)
  let branch := .cond (compare (.bvar 1)) pl(#true)
    (.cond (compare (.bvar 0)) retry pl(#false))
  let upper := .cond pl(#int ((n + 1 : ℕ) : ℤ) % #2 = #0)
    (.app (.app Occil.FactoryExtra.addFraction lo.encode.fst) (.bvar 1)) hi.encode.fst
  let lower := .cond pl(#int ((n + 1 : ℕ) : ℤ) % #2 = #1)
    (.app (.app Occil.FactoryExtra.subtractFraction hi.encode.fst) (.bvar 0)) lo.encode.fst
  let term := .cond pl(#bool b) (.app coefficient.fst pl(#int ((n + 1 : ℕ) : ℤ)))
    pl((#0, #1))
  bind term (bind lower (bind upper branch))

private theorem zero_fraction {rT : Type} :
    ((Fraction.ofRat 0).encode : Val rT).fst = pl((#0, #1)) := rfl

private theorem odd_test (n : ℕ) :
    ((((n + 1 : ℕ) : ℤ) % 2 == 1) = true) ↔ (n + 1) % 2 = 1 := by
  rw [beq_iff_eq]
  omega

private theorem even_test (n : ℕ) :
    ((((n + 1 : ℕ) : ℤ) % 2 == 0) = true) ↔ (n + 1) % 2 = 0 := by
  rw [beq_iff_eq]
  omega

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_fractionChoice (E : CoPset) (l : Loc) (a : Fraction) (q : List Bool)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (yes no : Exp rT) (Φ : Val rT → IProp GF)
    (hyes : ∀ s : List Bool, q <+: s → DyadicPosterior.resolves s (a.value : ℝ) true →
      iprop(UniformBag.owns l s ∗ ↯ (DyadicPosterior.credit s G)) ⊢ tglWp E yes Φ)
    (hno : ∀ s : List Bool, q <+: s → DyadicPosterior.resolves s (a.value : ℝ) false →
      iprop(UniformBag.owns l s ∗ ↯ (DyadicPosterior.credit s G)) ⊢ tglWp E no Φ) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q G)) ⊢
      tglWp E (fractionChoice l a yes no) Φ := by
  iintro H
  iterate 2 twp_pure
  simp only [Exp.ofVal]
  ieval (
    change _ ⊢ tglWp E
      (UniformBag.choice l a.numerator a.denominator yes no) Φ)
  iapply UniformBag.twp_choice E l q a.numerator a.denominator
    (by exact_mod_cast a.positive) G hG yes no Φ ?_ ?_
  · intro s hs ht
    iapply hyes s hs (by simpa only [Fraction.cast_value, Int.cast_natCast] using ht)
  · intro s hs ht
    iapply hno s hs (by simpa only [Fraction.cast_value, Int.cast_natCast] using ht)
  · iexact H

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_afterTerm (E : CoPset) (self : Val rT) (l : Loc) (n : ℕ)
    (lo hi c : Fraction) (b : Bool) (Φ : Val rT → IProp GF) :
    tglWp E (prepared self l n
      (stepLower n lo hi c b) (stepUpper n lo hi c b) b) Φ ⊢
      tglWp E (afterTerm self l n lo hi (stepTerm c b) b) Φ := by
  by_cases hn : (n + 1) % 2 = 1
  · have he : (n + 1) % 2 ≠ 0 := by omega
    have ho : (((n + 1 : ℕ) : ℤ) % 2 == 1) = true := (odd_test n).mpr hn
    have hz : (((n + 1 : ℕ) : ℤ) % 2 == 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      omega
    iintro H
    twp_pures
    rw [int_beq, ho]
    twp_pure
    twp_bind pl(&Occil.FactoryExtra.subtractFraction &hi.encode.fst &(stepTerm c b).encode.fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_subtractFraction E hi (stepTerm c b)
    iintro %v %hv
    subst v
    twp_pures
    rw [int_beq, hz]
    iterate 2 twp_pure
    isimp only [prepared, fractionChoice, stepLower, stepUpper, hn, he, ite_true,
      ite_false, one_ne_zero, zero_ne_one, Fraction.encode_ofRat] at H
    simp only [UniformBag.uniformBagLess_openRec]
    iexact H
  · have he : (n + 1) % 2 = 0 := by omega
    have ho : (((n + 1 : ℕ) : ℤ) % 2 == 1) = false := by
      apply beq_eq_false_iff_ne.mpr
      omega
    have hz : (((n + 1 : ℕ) : ℤ) % 2 == 0) = true := (even_test n).mpr he
    iintro H
    twp_pures
    rw [int_beq, ho]
    iterate 2 twp_pure
    twp_pures
    rw [int_beq, hz]
    twp_pure
    twp_bind pl(&Occil.FactoryExtra.addFraction &lo.encode.fst &(stepTerm c b).encode.fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_addFraction E lo (stepTerm c b)
    iintro %v %hv
    subst v
    twp_pure
    isimp only [prepared, fractionChoice, stepLower, stepUpper, hn, he, ite_true,
      ite_false, one_ne_zero, zero_ne_one, Fraction.encode_ofRat] at H
    simp only [UniformBag.uniformBagLess_openRec]
    iexact H

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_afterCoin (E : CoPset) (self coefficient : Val rT) (l : Loc) (n : ℕ)
    (lo hi c : Fraction) (b : Bool) (Φ : Val rT → IProp GF)
    (hcoefficient : ⊢ tglWp E pl(&coefficient.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = c.encode⌝))) :
    tglWp E (afterTerm self l n lo hi (stepTerm c b) b) Φ ⊢
      tglWp E (afterCoin self coefficient l n lo hi b) Φ := by
  cases b
  · iintro H
    iterate 2 twp_pure
    isimp only [stepTerm, Bool.false_eq_true, ite_false] at H
    isimp only [afterTerm, zero_fraction] at H
    simp only [ClosedExp.openRec, UniformBag.uniformBagLess_openRec]
    iexact H
  · iintro H
    twp_pure
    twp_bind pl(&coefficient.fst #int ((n + 1 : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply hcoefficient
    iintro %v %hv
    subst v
    twp_pure
    isimp only [stepTerm, ite_true] at H
    isimp only [afterTerm] at H
    simp only [ClosedExp.openRec, UniformBag.uniformBagLess_openRec]
    iexact H

private def loopValue (coin coefficient : Val rT) (l : Loc) : Val rT :=
  ⟨loop coin coefficient l, .fix (loop_locallyClosed coin coefficient l),
    loop_locallyClosed coin coefficient l⟩

private def draw (raw : ℕ → Fraction) (coin coefficient : Val rT) (l : Loc) (n : ℕ) : Exp rT :=
  pl(&(loop coin coefficient l) #int ((n + 1 : ℕ) : ℤ)
    &((state raw n).1).encode.fst &((state raw n).2).encode.fst #true)

private theorem twp_round (E : CoPset) (a : Parameters) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (p : unitInterval)
    (coin coefficient : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcoefficient : ∀ n : ℕ, ⊢ tglWp E pl(&coefficient.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)))
    (l : Loc) (N n : ℕ) (F : Bool → ℝ≥0∞)
    (hcontinue : ∀ q : List Bool,
      DyadicPosterior.resolves q (lower a (n + 1)) false →
      DyadicPosterior.resolves q (upper a (n + 1)) true →
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (horizonCredit a p (N + 1) (n + 1) F))) ⊢
        tglWp E (draw raw coin coefficient l (n + 1))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit a p (N + 1) n F))) ⊢
      tglWp E (draw raw coin coefficient l n)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro ⟨Hbag, Hcredit⟩
  twp_pures
  simp only [ClosedExp.openRec, UniformBag.uniformBagLess_openRec]
  twp_bind pl(&coin.fst #())
  isimp only [← expectation a p q (N + 1) n F] at Hcredit
  iapply (hcoin.wp (fun b => DyadicPosterior.credit q (branchCredit a p (N + 1) n F b))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pure
  simp only [ClosedExp.openRec, UniformBag.uniformBagLess_openRec]
  ieval (
    change _ ⊢ tglWp E
      (afterCoin (loopValue coin coefficient l) coefficient l n
        (state raw n).1 (state raw n).2 b) _)
  iapply twp_afterCoin E (loopValue coin coefficient l) coefficient l n
    (state raw n).1 (state raw n).2 (raw (n + 1)) b _ (hcoefficient (n + 1))
  iapply twp_afterTerm E (loopValue coin coefficient l) l n
    (state raw n).1 (state raw n).2 (raw (n + 1)) b
  isimp only [prepared]
  iapply twp_fractionChoice E l
    (stepLower n (state raw n).1 (state raw n).2 (raw (n + 1)) b) q
    (branchCredit a p (N + 1) n F b) (measurable_branchCredit a p (N + 1) n F b)
    pl(#true) _ _ ?_ ?_
  · intro r _ hlo
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists true
    ihave Hcredit := ErrorCredit.weaken
      (branch_lower_credit a p raw hraw (N + 1) n r F b hlo) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r _ hlo
    iintro ⟨Hbag, Hcredit⟩
    iapply twp_fractionChoice E l
      (stepUpper n (state raw n).1 (state raw n).2 (raw (n + 1)) b) r
      (branchCredit a p (N + 1) n F b) (measurable_branchCredit a p (N + 1) n F b)
      _ pl(#false) _ ?_ ?_
    · intro s hs hhi
      iintro ⟨Hbag, Hcredit⟩
      have hlo' := DyadicPosterior.resolves_refines hs hlo
      obtain ⟨rfl, hlo', hhi'⟩ := retry_resolves a raw hraw n s b hlo' hhi
      isimp only [branchCredit, ite_true] at Hcredit
      twp_pure
      rw [← Nat.cast_add_one]
      have hc := hcontinue s hlo' hhi'
      simp only [draw, state] at hc
      isimp only [loopValue, Exp.ofVal]
      iapply hc
      iframe Hbag Hcredit
    · intro s _ hhi
      iintro ⟨Hbag, Hcredit⟩
      twp_value
      imodintro
      iexists false
      ihave Hcredit := ErrorCredit.weaken
        (branch_upper_credit a p raw hraw (N + 1) n s F b hhi) $$ Hcredit
      iframe Hcredit
      itrivial
    · iframe Hbag Hcredit
  · iframe Hbag Hcredit

private theorem twp_until (E : CoPset) (a : Parameters) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (p : unitInterval)
    (coin coefficient : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcoefficient : ∀ n : ℕ, ⊢ tglWp E pl(&coefficient.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)))
    (l : Loc) (N n : ℕ) (hn : n ≤ N) (F : Bool → ℝ≥0∞) (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit a p (N + 1) n F))) ⊢
      tglWp E (draw raw coin coefficient l n)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hall : ∀ n ≤ N, ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (horizonCredit a p (N + 1) n F))) ⊢
        tglWp E (draw raw coin coefficient l n)
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (horizonCredit a p (N + 1) n F))) ⊢
        tglWp E (draw raw coin coefficient l n)
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) ?_ ?_ hn
    · intro n _ IH q
      iapply twp_round E a raw hraw p coin coefficient hcoin hcoefficient l N n F
        (fun q _ _ => IH q) q
    · intro q
      iapply twp_round E a raw hraw p coin coefficient hcoin hcoefficient l N N F ?_ q
      intro q hlo hhi
      iintro ⟨Hbag, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict (unresolved_credit a p (N + 1) q F hlo hhi) $$ Hcredit
  exact hall n hn q

private theorem twp_initialize (E : CoPset) (raw : ℕ → Fraction)
    (coin coefficient : Val rT)
    (hzero : ⊢ tglWp E pl(&coefficient.fst #0)
      (fun v : Val rT => iprop(⌜v = (raw 0).encode⌝)))
    (C : ℝ≥0∞) (Φ : Val rT → IProp GF)
    (hcontinue : ∀ l : Loc, iprop(UniformBag.owns l [] ∗ ↯ C) ⊢
      tglWp E (draw raw coin coefficient l 0) Φ) :
    ⊢ ↯ C -∗ tglWp E
      pl(&Occil.FactoryExtra.alternatingSeries &coin.fst &coefficient.fst #()) Φ := by
  rw [source_eq]
  iintro Hcredit
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill [.appL coefficient, .appL Val.unit] (.app (.lam sourceBody) coin.fst)) _)
  iapply (twp_beta E [.appL coefficient, .appL Val.unit] sourceBody coin
    source_locallyClosed _)
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill [.appL Val.unit] (.app (.lam (coefficientBody coin)) coefficient.fst)) _)
  iapply (twp_beta E [.appL Val.unit] (coefficientBody coin) coefficient
    (coefficient_locallyClosed coin) _)
  ieval (
    change _ ⊢ tglWp E
      (Ectx.fill ([] : Ectx rT) (.app (.lam (unitBody coin coefficient)) Val.unit.fst)) _)
  iapply (twp_beta E [] (unitBody coin coefficient) Val.unit
    (unit_locallyClosed coin coefficient) _)
  ieval (change _ ⊢ tglWp E (Exp.open' (unitBody coin coefficient) Val.unit.fst) _)
  rw [opened_unit]
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (bagBody coin coefficient)) (Val.loc l).fst)) _)
  iapply (twp_beta E [] (bagBody coin coefficient) (Val.loc l)
    (bag_locallyClosed coin coefficient) _)
  ieval (change _ ⊢ tglWp E (Exp.open' (bagBody coin coefficient) (Val.loc l).fst) _)
  rw [opened_bag]
  twp_bind pl(&coefficient.fst #0)
  iapply tglWp_wand
  isplitl []
  · iapply hzero
  iintro %v %hv
  subst v
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam (initialBody coin coefficient l)) (raw 0).encode.fst)) _)
  iapply (twp_beta E [] (initialBody coin coefficient l) (raw 0).encode
    (initial_locallyClosed coin coefficient l) _)
  ieval (
    change _ ⊢ tglWp E
      (Exp.open' (initialBody coin coefficient l) (raw 0).encode.fst) _)
  rw [opened_initial]
  ieval (
    change _ ⊢ tglWp E (Ectx.fill ([] : Ectx rT)
      (.app (.lam pl({Exp.bvar 0} #1 (#0, #1) &(raw 0).encode.fst #true))
        (loopValue coin coefficient l).fst)) _)
  iapply (twp_beta E [] pl({Exp.bvar 0} #1 (#0, #1) &(raw 0).encode.fst #true)
    (loopValue coin coefficient l) (by is_lc) _)
  simp only [Ectx.fill_nil, Exp.open', Exp.openRec, openRec_val_fst]
  ieval (change _ ⊢ tglWp E (draw raw coin coefficient l 0) _)
  iapply hcontinue l
  iframe Hbag Hcredit

/-- The actual rational accumulator, with one shared cached uniform and an abstract input coin. -/
theorem twp_alternatingSeries (E : CoPset) (a : Parameters) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (p : unitInterval)
    (coin coefficient : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcoefficient : ∀ n : ℕ, ⊢ tglWp E pl(&coefficient.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (meanBias a p) F) -∗
      tglWp E pl(&Occil.FactoryExtra.alternatingSeries &coin.fst &coefficient.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := exists_horizon a p F δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  iapply (twp_initialize E raw coin coefficient (hcoefficient 0) _ _ ?_) $$ Hcredit
  intro l
  iapply twp_until E a raw hraw p coin coefficient hcoin hcoefficient l N 0
    (Nat.zero_le _) F []

/-- Every nonnegative decreasing rational coefficient sequence tending to zero. -/
theorem alternatingSeries_distSpec (E : CoPset) (a : Parameters) (raw : ℕ → Fraction)
    (hraw : ∀ n, (raw n).value = a.coefficient n) (p : unitInterval)
    (coin coefficient : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (hcoefficient : ∀ n : ℕ, ⊢ tglWp E pl(&coefficient.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = (raw n).encode⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.alternatingSeries
      &coin.fst &coefficient.fst #()) (RealCoin.law (meanBias a p)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_alternatingSeries E a raw hraw p coin coefficient hcoin hcoefficient F)

end specification

end

end SampLib.AlternatingSeries
