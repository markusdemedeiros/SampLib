import SampLib.Constants.Laws.UniformVectorCoin
import SampLib.Latent.LatentCoinSpec
import SampLib.Latent.UniformVectorOwnership
import SampLib.Bernoulli.SampleGeometricBag

/-! # Geometric-bag calls preserve a jointly owned uniform vector -/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformVector

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal LatentReal.LatentCoin

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A call refines only the selected cache and keeps every joint continuation dependency. -/
theorem twp_coordinateCoin (E : CoPset) {n : ℕ} (roots : Fin n → Loc)
    (p : Fin n → List Bool) (i : Fin n)
    (G : Bool → (Fin n → ℝ) → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(rootsOwns roots p ∗ ↯ (credit (world n) p (coinBias i) G)) ⊢
      tglWp E pl(&Occil.sampleGeometricBag #loc (roots i) #())
        (post (world n) (fun _ => rootsOwns roots) Val.unit p G) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    iintro ⟨Hstate, Hcredit⟩
    ihave ⟨Hi, Hrestore⟩ := access roots p i $$ Hstate
    isimp only [coin_expectation p i G hG] at Hcredit
    iapply tglWp_wand
    isplitl [Hi Hcredit]
    · iapply SampleGeometricBag.twp_sampleGeometricBag E (roots i) (p i)
        (fun b => coordinateCredit p i (G b))
        (fun b => measurable_coordinateCredit p i (hG b))
      iframe Hi Hcredit
    iintro %v Hpost
    isimp only [UniformBag.coinPost] at Hpost
    icases Hpost with ⟨%b, %q, %hv, Hi, Hcredit⟩
    rcases hv with ⟨rfl, hpq⟩
    ihave Hstate := Hrestore $$ %q Hi
    isimp only [DyadicPosterior.credit, ← expectation_update p i q (G b) (hG b)] at Hcredit
    iapply post_return (world (n + 1)) (fun _ => rootsOwns roots) Val.unit p
      (Function.update p i q) b G (refines_update p i q hpq)
    isimp only [world]
    iframe Hstate Hcredit

end specification

end

end SampLib.UniformVector
