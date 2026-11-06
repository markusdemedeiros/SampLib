import SampLib.Core.ListEncoding
import SampLib.Uniform.UniformInt
import SampLib.Combinatorial.Laws.Choice
import Samplers.Combinatorial.Basic
import Metrology.Iris.LocalBI

/-!
# Uniform list choice

The mathematical output is a uniformly sampled position, encoded by its list
entry. Equal entries retain their separate positions and hence multiplicities.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.Choice

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

/-- CTE specification for any nonempty list, with arbitrary element values. -/
theorem twp_choice (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] (F : Fin xs.length → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂law xs.length) -∗
      tglWp E pl(&Occil.choice &(listVal encode xs).fst)
        (fun v : Val rT => iprop(∃ i : Fin xs.length,
          ⌜v = encode (xs.get i)⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  twp_pure
  twp_bind pl(&Occil.length &(listVal encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply (twp_length E encode xs)
  iintro %v %hv
  subst v
  twp_bind pl(&Occil.uniformInt #int (xs.length : ℤ))
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (UniformInt.twp_uniformInt E xs.length (NeZero.pos xs.length)
      (fun k => F (position xs.length k)))
    rw [← lintegral_law]
    iexact Hcredit
  iintro %v ⟨%k, %hv, %hk, Hcredit⟩
  subst v
  twp_bind pl(&Occil.getAt &(listVal encode xs).fst #int (k : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply (twp_getAt E encode xs ⟨k, hk⟩)
  iintro %v %hv
  iapply (tglWp_value (v := v))
  iexists ⟨k, hk⟩
  isimp only [position_of_lt k hk] at Hcredit
  iframe Hcredit
  ipureintro
  exact hv

/-- Typed specification using latent positions and their list entries. -/
theorem choice_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] :
    IsDistSpec (GF := GF) E pl(&Occil.choice &(listVal encode xs).fst)
      (law xs.length) (fun i => encode (xs.get i)) where
  spec F _ := wand_entails (twp_choice E encode xs F)

end specification

end

end SampLib.Choice
