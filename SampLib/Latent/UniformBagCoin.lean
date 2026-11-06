import SampLib.Latent.UniformBag
import SampLib.Latent.Laws.LatentBernoulli

/-! # Conditional coin specifications for shared uniform bags

The expected continuation depends on both the result and the original latent
uniform. Each call retains the actual bag and its refined posterior; repeating a
call therefore preserves conditional independence without discarding correlation.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

noncomputable section

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF] [ECGS GF]
local bi (IProp GF)

/-- A conditional output retains the original root and its updated cached prefix. -/
def coinPost (l : Loc) (p : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (v : Val rT) : IProp GF := iprop(∃ (b : Bool) (q : List Bool),
  ⌜v = Val.bool b ∧ p <+: q⌝ ∗ owns l q ∗ ↯ (DyadicPosterior.credit q (G b)))

/-- Return a known bit after any refinement of the original cache. -/
theorem coinPost_return (l : Loc) (p q : List Bool) (b : Bool)
    (G : Bool → ℝ → ℝ≥0∞) (hpq : p <+: q) :
    iprop(owns l q ∗ ↯ (DyadicPosterior.credit q (G b))) ⊢ coinPost l p G (Val.bool b) := by
  iintro ⟨Hbag, Hcredit⟩
  isimp only [coinPost]
  iexists b, q
  iframe Hbag Hcredit
  ipureintro
  exact ⟨rfl, hpq⟩

/-- A composed call also refines every earlier cache prefix. -/
theorem coinPost_weaken (l : Loc) (p q : List Bool) (G : Bool → ℝ → ℝ≥0∞)
    (v : Val rT) (hpq : p <+: q) : coinPost l q G v ⊢ coinPost l p G v := by
  iintro Hpost
  isimp only [coinPost] at Hpost
  ihave ⟨%b, %r, %hr, Hbag, Hcredit⟩ := Hpost
  isimp only [coinPost]
  iexists b, r
  iframe Hbag Hcredit
  ipureintro
  exact ⟨hr.1, hpq.trans hr.2⟩

end ownership

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A stateful Bernoulli kernel relative to the same shared latent uniform. -/
structure IsCoinSpec (E : CoPset) (l : Loc) (e : Exp rT) (φ : ℝ → unitInterval) : Prop where
  measurable_bias : Measurable φ
  spec (p : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(owns l p ∗ ↯ (LatentBernoulli.credit p φ G)) ⊢
      tglWp E e (coinPost l p G)

namespace IsCoinSpec

/-- Supply a conditional continuation while retaining unrelated caller resources. -/
theorem wp {E : CoPset} {l : Loc} {e : Exp rT} {φ : ℝ → unitInterval}
    (h : IsCoinSpec (GF := GF) E l e φ) (p : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (Φ : Val rT → IProp GF) :
    ⊢ owns l p -∗ ↯ (LatentBernoulli.credit p φ G) -∗
      (∀ (b : Bool) (q : List Bool), ⌜p <+: q⌝ -∗ owns l q -∗
        ↯ (DyadicPosterior.credit q (G b)) -∗ Φ (Val.bool b)) -∗ tglWp E e Φ := by
  iintro Hbag Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply h.spec p G hG
    iframe Hbag Hcredit
  iintro %v Hpost
  isimp only [coinPost] at Hpost
  ihave ⟨%b, %q, %hq, Hbag, Hcredit⟩ := Hpost
  rcases hq with ⟨rfl, hpq⟩
  iapply Hcont $$ %b %q %hpq Hbag Hcredit

end IsCoinSpec

end specification

end

end SampLib.UniformBag
