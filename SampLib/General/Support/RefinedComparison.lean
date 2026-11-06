import SampLib.Common.Laws.RefinedComparison
import SampLib.General.Syntax.RefinedComparison
import SampLib.Latent.UniformBagCoin

/-! # Refinement relative to an owned cached uniform

A finite uncertainty horizon establishes termination without a convergence rate.
The returned bit keeps both the cache and its conditional continuation credit.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RefinedComparison

noncomputable section

/-- The callback returns the lower and upper dyadic numerators. -/
def encodeInterval {rT : Type} {p : unitInterval} (a : FromBounds.Interval p) : Val rT :=
  .pair (.int a.lower) (.int a.upper)

private theorem ordered {p : unitInterval} (a : FromBounds.Interval p) :
    a.lower ≤ a.upper := by exact_mod_cast a.below.trans a.above

private theorem valid_guard {p : unitInterval} (a : FromBounds.Interval p)
    (hlo : 0 ≤ a.lower) (hhi : a.upper ≤ a.denominator) :
    Bool.or (Bool.or (decide (a.lower < 0)) (decide (a.upper < a.lower)))
      (decide ((a.denominator : ℤ) < a.upper)) = false := by
  simp [not_lt.mpr hlo, not_lt.mpr (ordered a), not_lt.mpr hhi]

private theorem next_denominator {p : unitInterval} (a : ℕ → FromBounds.Interval p)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (n : ℕ) :
    ((a n).denominator : ℤ) * 2 = ((a (n + 1)).denominator : ℤ) := by
  have h : (a (n + 1)).denominator = (a n).denominator * 2 := by
    simp only [hden, pow_succ]
  exact_mod_cast h.symm

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF] [ECGS GF]
local bi (IProp GF)

/-- A comparison returns its cache and the exact comparison fact learned about its latent value. -/
def post (l : Loc) (q : List Bool) (p : unitInterval)
    (G : Bool → ℝ → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ (b : Bool) (r : List Bool),
    ⌜v = Val.bool b ∧ q <+: r ∧ DyadicPosterior.resolves r (p : ℝ) b⌝ ∗
      UniformBag.owns l r ∗ ↯ (DyadicPosterior.credit r (G b)))

end ownership

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

set_option maxHeartbeats 1000000 in
private theorem twp_round (E : CoPset) (p : unitInterval) (a : ℕ → FromBounds.Interval p)
    (hlo : ∀ n, 0 ≤ (a n).lower) (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (lookup : Exp rT)
    (hlookup : lookup.IsLocallyClosed)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&lookup #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝)))
    (l : Loc) (N n : ℕ) (q₀ q : List Bool) (hq : q₀ <+: q)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b))
    (hcontinue : ∀ r : List Bool, q <+: r →
      DyadicPosterior.resolves r (a n).left false →
      DyadicPosterior.resolves r (a n).right true →
      iprop(UniformBag.owns l r ∗
        ↯ (DyadicPosterior.credit r (horizonCredit (a N) G))) ⊢
        tglWp E pl(&(Program.loop lookup l)
          #int ((n + 2 : ℕ) : ℤ) #int ((a (n + 1)).denominator : ℤ)) (post l q₀ p G)) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) G))) ⊢
      tglWp E pl(&(Program.loop lookup l)
        #int ((n + 1 : ℕ) : ℤ) #int ((a n).denominator : ℤ)) (post l q₀ p G) := by
  iintro ⟨Hbag, Hcredit⟩
  have hopen (k : ℕ) (e : Exp rT) : Exp.openRec k e lookup = lookup :=
    (Exp.open_lc k e lookup hlookup).symm
  twp_pures
  simp only [hopen, UniformBag.uniformBagLess_openRec]
  ieval (
    change _ ⊢ tglWp E
      (Program.round lookup (Program.loop lookup l) l (n + 1) (a n).denominator) _)
  rw [← Program.loopValue_fst lookup l hlookup]
  twp_bind pl(&lookup #int ((n + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hbounds n
  iintro %v %hv
  subst v
  iterate 10 twp_pure
  rw [valid_guard (a n) (hlo n) (hhi n)]
  twp_pure
  rw [Program.loopValue_fst lookup l hlookup]
  ieval (
    change _ ⊢ tglWp E
      (UniformBag.bracket l (a n).lower (a n).denominator (a n).upper (a n).denominator
        pl(#true) pl(#false)
        pl(&(Program.loop lookup l) (#int ((n + 1 : ℕ) : ℤ) + #1)
          (#int ((a n).denominator : ℤ) * #2))) _)
  iapply UniformBag.twp_bracket E l q _ _ _ _
    (by exact_mod_cast (a n).positive) (by exact_mod_cast (a n).positive)
    (horizonCredit (a N) G) (measurable_horizonCredit (a N) G hG)
    pl(#true) pl(#false)
    pl(&(Program.loop lookup l) (#int ((n + 1 : ℕ) : ℤ) + #1)
      (#int ((a n).denominator : ℤ) * #2)) _ ?_ ?_ ?_
  · intro r hr hlower
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    isimp only [post]
    iexists true, r
    have hp := lower_resolves (a n) r hlower
    ihave Hcredit := ErrorCredit.weaken (return_credit (a N) r G true hp) $$ Hcredit
    iframe Hbag Hcredit
    ipureintro
    exact ⟨rfl, hq.trans hr, hp⟩
  · intro r hr _ hupper
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    isimp only [post]
    iexists false, r
    have hp := upper_resolves (a n) r hupper
    ihave Hcredit := ErrorCredit.weaken (return_credit (a N) r G false hp) $$ Hcredit
    iframe Hbag Hcredit
    ipureintro
    exact ⟨rfl, hq.trans hr, hp⟩
  · intro r hr hlower hupper
    iintro ⟨Hbag, Hcredit⟩
    iterate 2 twp_pure
    simp only [← Nat.cast_add_one, Exp.ofVal]
    rw [next_denominator a hden n]
    iapply hcontinue r hr hlower hupper
    iframe Hbag Hcredit
  · iframe Hbag Hcredit

private theorem twp_until (E : CoPset) (p : unitInterval) (a : ℕ → FromBounds.Interval p)
    (hlo : ∀ n, 0 ≤ (a n).lower) (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (lookup : Exp rT)
    (hlookup : lookup.IsLocallyClosed)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&lookup #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝)))
    (l : Loc) (N n : ℕ) (hn : n ≤ N) (q₀ q : List Bool) (hq : q₀ <+: q)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) G))) ⊢
      tglWp E pl(&(Program.loop lookup l)
        #int ((n + 1 : ℕ) : ℤ) #int ((a n).denominator : ℤ)) (post l q₀ p G) := by
  have hall : ∀ n ≤ N, ∀ q : List Bool, q₀ <+: q →
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) G))) ⊢
        tglWp E pl(&(Program.loop lookup l)
          #int ((n + 1 : ℕ) : ℤ) #int ((a n).denominator : ℤ)) (post l q₀ p G) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ q : List Bool, q₀ <+: q →
      iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit (a N) G))) ⊢
        tglWp E pl(&(Program.loop lookup l)
          #int ((n + 1 : ℕ) : ℤ) #int ((a n).denominator : ℤ)) (post l q₀ p G)) ?_ ?_ hn
    · intro n hn IH q hq
      iapply twp_round E p a hlo hhi hden lookup hlookup hbounds l N n q₀ q hq G hG
        (fun r hr _ _ => IH r (hq.trans hr))
    · intro q hq
      iapply twp_round E p a hlo hhi hden lookup hlookup hbounds l N N q₀ q hq G hG ?_
      intro r hr hlower hupper
      iintro ⟨Hbag, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict (unresolved_credit (a N) r G hlower hupper) $$ Hcredit
  exact hall n hn q hq

/-- Every initial cache and measurable joint continuation admit a finite uncertainty horizon. -/
theorem twp_loop (E : CoPset) (p : unitInterval) (a : ℕ → FromBounds.Interval p)
    (ha : FromBounds.Tight a) (hlo : ∀ n, 0 ≤ (a n).lower)
    (hhi : ∀ n, (a n).upper ≤ (a n).denominator)
    (hden : ∀ n, (a n).denominator = 2 ^ (n + 1)) (lookup : Exp rT)
    (hlookup : lookup.IsLocallyClosed)
    (hbounds : ∀ n : ℕ, ⊢ tglWp E pl(&lookup #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeInterval (a n)⌝)))
    (l : Loc) (q : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (outputCredit p G))) ⊢
      tglWp E pl(&(Program.loop lookup l) #1 #2) (post l q p G) := by
  iintro ⟨Hbag, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := exists_horizon a ha q G hG δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  have hstart : ((a 0).denominator : ℤ) = 2 := by simp [hden]
  rw [← hstart]
  iapply twp_until E p a hlo hhi hden lookup hlookup hbounds l N 0 (Nat.zero_le _) q q
    (List.prefix_refl _) G hG
  iframe Hbag Hcredit

end specification

end

end SampLib.RefinedComparison
