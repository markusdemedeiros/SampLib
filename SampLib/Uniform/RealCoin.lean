import SampLib.Templates
import SampLib.Uniform.Laws.RealCoin
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-!
# Continuous threshold Bernoulli sampler

`realCoin_distSpec` verifies `Occil.realCoin` over mathematical reals for every
`p ∈ [0, 1]`. The law and its uniform credit kernel live in `Uniform/Laws/RealCoin`.
-/

open Set ProbLang
open ProbLangℝ (realLt realOfInt)
open scoped ENNReal

namespace SampLib.RealCoin

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

/-- Unit-interval inputs pass the domain check. -/
private theorem realCoin_guard (p : unitInterval) :
    (realLt (p : ℝ) (realOfInt 0) || realLt (realOfInt 1) (p : ℝ)) = false := by
  simp [realLt, realOfInt, not_lt.mpr p.2.1, not_lt.mpr p.2.2]

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- CTE specification with arbitrary continuation credits. -/
theorem twp_realCoin (E : CoPset) (p : unitInterval) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (credit p F) -∗
      tglWp E pl(&Occil.realCoin #real (p : ℝ))
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v.1 = .lit (.bool b)⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  twp_pures
  rw [realCoin_guard p]
  twp_pures
  -- Redistribute the initial credit across the uniform draw.
  twp_bind pl(urand)
  iapply (twp_urand_exp (measurable_uniformCredit p F) ?_) $$ Hcredit
  · rw [lintegral_uniformCredit]
  iintro %r ⟨_, Hcredit⟩
  twp_pures
  twp_value
  imodintro
  iexists (decide (r < (p : ℝ)))
  -- The sampled credit is exactly the continuation credit of this result.
  isimp only [uniformCredit_eq] at Hcredit
  iframe Hcredit
  ipureintro
  rfl

/-- Typed distribution specification. -/
theorem realCoin_distSpec (E : CoPset) (p : unitInterval) :
    IsDistSpec (GF := GF) E pl(&Occil.realCoin #real (p : ℝ)) (law p) Val.bool where
  spec F _ := by
    simpa only [lintegral_law, Val.ext_iff] using wand_entails (twp_realCoin E p F)

end specification

end

end SampLib.RealCoin
