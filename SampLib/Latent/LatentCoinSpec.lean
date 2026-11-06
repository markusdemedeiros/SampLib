import SampLib.Latent.LatentSpec
import SampLib.Latent.Laws.LatentCoin
import SampLib.Uniform.RealCoin

/-! # Conditional coins over an owned latent world

A coin can depend on a shared deferred real without revealing its value. The
credit kernel retains both the returned bit and the whole latent state; observing
a second such coin therefore does not assert independence of their marginals.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

section specification

open LatentCoin

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A coin outcome retains the same source handle at a refined posterior state. -/
def LatentCoin.post (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ (b : Bool) (t : S), ⌜result = Val.bool b ∧ D.refines s t⌝ ∗
    owns source t ∗ ↯ (∫⁻ x, G b x ∂D.posterior t))

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
/-- Return an outcome with its refined state and unspent joint credit. -/
theorem LatentCoin.post_return (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (source : Val rT) (s t : S) (b : Bool) (G : Bool → Ω → ℝ≥0∞)
    (hst : D.refines s t) :
    iprop(owns source t ∗ ↯ (∫⁻ x, G b x ∂D.posterior t)) ⊢
      post D owns source s G (Val.bool b) := by
  iintro ⟨Hstate, Hcredit⟩
  isimp only [post]
  iexists b, t
  iframe Hstate Hcredit
  ipureintro
  exact ⟨rfl, hst⟩

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
/-- A continuation may forget an intermediate refinement without changing its credit. -/
theorem LatentCoin.post_weaken (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (source : Val rT) (s t : S) (G : Bool → Ω → ℝ≥0∞) (result : Val rT)
    (hst : D.refines s t) :
    post D owns source t G result ⊢ post D owns source s G result := by
  iintro Hpost
  isimp only [post] at Hpost
  icases Hpost with ⟨%b, %u, %hu, Hstate, Hcredit⟩
  isimp only [post]
  iexists b, u
  iframe Hstate Hcredit
  ipureintro
  exact ⟨hu.1, D.refines_trans hst hu.2⟩

/-- A conditional coin retains the source state and arbitrary joint output/latent credit.
The program may be a direct unary test or an application of a unit callback. -/
structure IsLatentCoinProgramSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (bias : Ω → unitInterval)
    (program : Val rT → Exp rT) : Prop where
  measurable_bias : Measurable bias
  spec (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞)
      (hG : ∀ b, Measurable (G b)) :
    iprop(owns source s ∗ ↯ (credit D s bias G)) ⊢
      tglWp E (program source) (post D owns source s G)

/-- Unit callbacks specialize the same conditional-program protocol. -/
abbrev IsLatentCoinSpec (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (bias : Ω → unitInterval)
    (coin : Val rT → Val rT) : Prop :=
  IsLatentCoinProgramSpec E D owns bias (fun source => pl(&(coin source).fst #()))

namespace IsLatentCoinProgramSpec

/-- A caller receives both the coin result and the same refined latent ownership. -/
theorem wp {E : CoPset} {D : Model Ω S} {owns : Val rT → S → IProp GF}
    {bias : Ω → unitInterval} {program : Val rT → Exp rT}
    (h : IsLatentCoinProgramSpec E D owns bias program) (source : Val rT) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (Φ : Val rT → IProp GF) :
    ⊢ owns source s -∗ ↯ (credit D s bias G) -∗
      (∀ (b : Bool) (t : S), ⌜D.refines s t⌝ -∗ owns source t -∗
        ↯ (∫⁻ x, G b x ∂D.posterior t) -∗ Φ (Val.bool b)) -∗
      tglWp E (program source) Φ := by
  iintro Hstate Hcredit Hcont
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply h.spec source s G hG
    iframe Hstate Hcredit
  iintro %result Hpost
  isimp only [post] at Hpost
  icases Hpost with ⟨%b, %t, %hresult, Hstate, Hcredit⟩
  rcases hresult with ⟨rfl, hrefines⟩
  iapply Hcont $$ %b %t %hrefines Hstate Hcredit

end IsLatentCoinProgramSpec
namespace IsLatentCoinSpec

/-- Continuation form for the unit-callback specialization. -/
theorem wp {E : CoPset} {D : Model Ω S} {owns : Val rT → S → IProp GF}
    {bias : Ω → unitInterval} {coin : Val rT → Val rT}
    (h : IsLatentCoinSpec E D owns bias coin) (source : Val rT) (s : S)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) (Φ : Val rT → IProp GF) :
    ⊢ owns source s -∗ ↯ (credit D s bias G) -∗
      (∀ (b : Bool) (t : S), ⌜D.refines s t⌝ -∗ owns source t -∗
        ↯ (∫⁻ x, G b x ∂D.posterior t) -∗ Φ (Val.bool b)) -∗
      tglWp E pl(&(coin source).fst #()) Φ :=
  IsLatentCoinProgramSpec.wp h source s G hG Φ

end IsLatentCoinSpec


end specification

end

end SampLib.LatentReal
