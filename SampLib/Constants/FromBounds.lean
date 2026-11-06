import SampLib.Constants.Support.FromBoundsEncoding
import SampLib.Latent.UniformBagBracket
import Samplers.Constants.Engines

/-! # Exact coins from arbitrarily tight rational enclosures

Choose one finite horizon whose uncertainty interval fits the error budget.
The shared-uniform credit pays every settled answer; at the horizon an unresolved
comparison owns one whole credit. No convergence rate is needed.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FromBounds

noncomputable section

private theorem denominator_pos {p : unitInterval} (a : Interval p) :
    (0 : ℤ) < a.denominator := by exact_mod_cast a.positive

private theorem ordered {p : unitInterval} (a : Interval p) : a.lower ≤ a.upper := by
  exact_mod_cast a.below.trans a.above

private theorem valid_guard {p : unitInterval} (a : Interval p) :
    (decide ((a.denominator : ℤ) ≤ 0) || decide (a.upper < a.lower)) = false := by
  simp [a.positive.ne', not_lt.mpr (ordered a)]

private theorem lower_resolves {p : unitInterval} (a : Interval p)
    {q r : List Bool} {b : Bool}
    (h : UniformBag.comparisonResult q a.lower a.denominator b r) :
    DyadicPosterior.resolves r a.left b := by
  simpa only [Interval.left, Int.cast_natCast] using h.2

private theorem upper_resolves {p : unitInterval} (a : Interval p)
    {q r : List Bool} {b : Bool}
    (h : UniformBag.comparisonResult q a.upper a.denominator b r) :
    DyadicPosterior.resolves r a.right b := by
  simpa only [Interval.right, Int.cast_natCast] using h.2

private def loop {rT : Type} (bounds : Val rT) (l : Loc) : Exp rT :=
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (.lit (.loc l))) x) (.bvar 0)
  let recur := .app (.bvar 5) (.binop .plus (.bvar 4) (.lit (.int 1)))
  let branch := .cond
    (.binop .or (.binop .le (.bvar 0) (.lit (.int 0))) (.binop .lt (.bvar 1) (.bvar 2)))
    .fail
    (.cond (compare (.bvar 2)) (.lit (.bool true))
      (.cond (compare (.bvar 1)) recur (.lit (.bool false))))
  .fix (.lam (.app (.lam
    (.app (.lam
      (.app (.lam
        (.app (.lam branch) (.snd (.snd (.bvar 2))))) (.fst (.snd (.bvar 1)))))
      (.fst (.bvar 0)))) (.app bounds.fst (.bvar 0))))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_round (E : CoPset) (p : unitInterval) (a : ℕ → Interval p)
    (bounds : Val rT)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝)))
    (l : Loc) (N n : ℕ) (F : Bool → ℝ≥0∞)
    (hcontinue : ∀ q : List Bool,
      DyadicPosterior.resolves q (a n).left false →
      DyadicPosterior.resolves q (a n).right true →
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) F))) ⊢
        tglWp E pl(&(loop bounds l) #int ((n + 1 : ℕ) : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) F))) ⊢
      tglWp E pl(&(loop bounds l) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro ⟨Hbag, Hcredit⟩
  twp_pures
  twp_bind pl(&bounds.fst #int (n : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hbounds n
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_guard (a n)]
  twp_pure
  simp only [UniformBag.uniformBagLess_openRec]
  ieval (
    change _ ⊢ tglWp E
      (UniformBag.bracket l (a n).lower (a n).denominator (a n).upper (a n).denominator
        pl(#true) pl(#false) pl(&(loop bounds l) (#int (n : ℤ) + #1))) _)
  iapply UniformBag.twp_bracket E l q _ _ _ _
    (denominator_pos (a n)) (denominator_pos (a n))
    (horizonCredit (a N) F) (measurable_horizonCredit (a N) F)
    pl(#true) pl(#false) pl(&(loop bounds l) (#int (n : ℤ) + #1)) _ ?_ ?_ ?_
  · intro r hr hlo
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists true
    ihave Hcredit := ErrorCredit.weaken
      (lower_credit (a n) (a N) r F (lower_resolves (a n) ⟨hr, hlo⟩)) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r hr _ hhi
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists false
    ihave Hcredit := ErrorCredit.weaken
      (upper_credit (a n) (a N) r F (upper_resolves (a n) ⟨hr, hhi⟩)) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r hr hlo hhi
    iintro ⟨Hbag, Hcredit⟩
    twp_pure
    rw [← Nat.cast_add_one]
    iapply hcontinue r (lower_resolves (a n) ⟨hr, hlo⟩) (upper_resolves (a n) ⟨hr, hhi⟩)
    iframe Hbag Hcredit
  · iframe Hbag Hcredit

private theorem twp_until (E : CoPset) (p : unitInterval) (a : ℕ → Interval p)
    (bounds : Val rT)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝)))
    (l : Loc) (N n : ℕ) (hn : n ≤ N) (F : Bool → ℝ≥0∞) (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) F))) ⊢
      tglWp E pl(&(loop bounds l) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hall : ∀ n ≤ N, ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) F))) ⊢
        tglWp E pl(&(loop bounds l) #int (n : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) F))) ⊢
        tglWp E pl(&(loop bounds l) #int (n : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) ?_ ?_ hn
    · intro n hn IH q
      iapply twp_round E p a bounds hbounds l N n F (fun q _ _ => IH q) q
    · intro q
      iapply twp_round E p a bounds hbounds l N N F ?_ q
      intro q hlo hhi
      iintro ⟨Hbag, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict (unresolved_credit (a N) q F hlo hhi) $$ Hcredit
  exact hall n hn q

/-- A finite uncertainty horizon pays for the actual shared-uniform refinement loop. -/
theorem twp_fromBounds (E : CoPset) (p : unitInterval) (a : ℕ → Interval p) (ha : Tight a)
    (bounds : Val rT)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit p F) -∗ tglWp E pl(&Occil.Constants.fromBounds &bounds.fst #())
      (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := exists_horizon a ha F δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  iterate 2 twp_pure
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  iterate 2 twp_pure
  have hloop := twp_until (rT := rT) (GF := GF) E p a bounds hbounds l N 0 (Nat.zero_le _) F []
  simp only [loop] at hloop
  simp only [UniformBag.uniformBagLess_closeRec, UniformBag.uniformBagLess_openRec]
  iapply hloop
  iframe Hbag Hcredit

/-- Exact Bernoulli sampling from arbitrary, arbitrarily tight rational enclosures. -/
theorem fromBounds_distSpec (E : CoPset) (p : unitInterval) (a : ℕ → Interval p) (ha : Tight a)
    (bounds : Val rT)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&bounds.fst #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝))) :
    IsDistSpec (GF := GF) E pl(&Occil.Constants.fromBounds &bounds.fst #())
      (RealCoin.law p) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_fromBounds E p a ha bounds hbounds F)

end specification

end

end SampLib.FromBounds
