import SampLib.BetaStep
import SampLib.UniformBag
import SampLib.LatentDigitSource

/-! # Allocating a conditional digit stream

The constructor allocates its cache without invoking the digit callback. In
particular it preserves every credit and unrelated owned resource unchanged.
-/

open ProbLang

namespace SampLib.LatentDigits

open scoped Syntax

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Allocation returns the exact callback-capturing closure and its physical root. -/
theorem twp_allocate (E : CoPset) (nextBit : Val rT) (R : IProp GF) :
    R ⊢ tglWp E pl(&Occil.PSRN.newByDigits &nextBit.fst #())
      (fun v : Val rT => iprop(∃ root : Loc,
        ⌜v = Syntax.oracleVal nextBit root⌝ ∗ UniformBag.owns root [] ∗ R)) := by
  iintro HR
  rw [← Syntax.source_fst]
  ieval (change _ ⊢ tglWp E (Ectx.fill [.appL (.unit : Val rT)]
    (.app (.lam (.lam Syntax.constructorBody)) nextBit.fst)) _)
  iapply (twp_beta E [.appL (.unit : Val rT)] (.lam Syntax.constructorBody)
    nextBit (Syntax.sourceVal (rT := rT)).lc _)
  simp only [Syntax.source_beta, Ectx.fill]
  ieval (change _ ⊢ tglWp E (.app (.lam (Syntax.partialBody nextBit)) (.lit .unit)) _)
  have hbeta := twp_beta (GF := GF) (rT := rT) E [] (Syntax.partialBody nextBit) (.unit : Val rT)
    (Syntax.partialVal nextBit).lc
  simp only [Ectx.fill, List.foldl_nil] at hbeta
  iapply hbeta
  simp only [Syntax.constructor_opened]
  twp_pure
  twp_bind pl(alloc(inl(#())))
  ieval (change _ ⊢ tglWp E (.alloc (.ofVal (Val.inl (Val.unit : Val rT)))) _)
  iapply (twp_alloc (v := Val.inl (Val.unit : Val rT)))
  iintro %root Hroot
  ieval (change _ ⊢ tglWp E (.app (.lam (Syntax.rootBody nextBit)) (.lit (.loc root))) _)
  iapply Syntax.twp_allocated_oracle E nextBit root _
  twp_value
  imodintro
  iexists root
  isimp only [UniformBag.owns, UniformBag.emptyVal]
  iframe Hroot HR
  ipureintro
  rfl

end specification

end SampLib.LatentDigits
