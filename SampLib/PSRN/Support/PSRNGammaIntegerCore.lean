import SampLib.PSRN.Support.LatentGammaIntegerModel
import SampLib.PSRN.Support.LatentProduct
import SampLib.PSRN.Support.LatentAddition
import SampLib.PSRN.Syntax.PSRNGammaInteger

/-! # The positive integer-gamma source from its exponential component

Every recursive step allocates a new independent exponential world, then returns
an addition oracle over the complete product state. Depth `n` means shape `n+1`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGammaInteger.Core

noncomputable section

open LatentReal
open scoped SampLib.PSRNGammaInteger.Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- A positive-depth sum retains every constituent handle exactly once. -/
def owns (O : Val rT → S → IProp GF) :
    (n : ℕ) → Val rT → LatentGammaInteger.State S n → IProp GF
  | 0 => O
  | n + 1 => fun v s => iprop(∃ (left right : Val rT),
    ViewOwns (addVal left right) (Product.owns O (owns O n) left right) v s)

/-- Reading a recursively nested sum preserves its entire independent product world. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (O : Val rT → S → IProp GF)
    (hO : IsOracleSpec E D O) (n : ℕ) :
    IsOracleSpec E (LatentGammaInteger.model D n) (owns O n) := by
  induction n with
  | zero => exact hO
  | succ n IH =>
    refine ⟨?_⟩
    intro v s precision F hF
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%left, %right, Hstate⟩
    have hleft := Product.left_viewSpec E D (LatentGammaInteger.model D n) O (owns O n)
      hO left right
    have hright := Product.right_viewSpec E D (LatentGammaInteger.model D n) O (owns O n)
      IH left right
    have hsum : IsOracleSpec E (LatentGammaInteger.model D (n + 1))
        (ViewOwns (addVal left right) (Product.owns O (owns O n) left right)) :=
      add_oracleSpec E _ _ (ProductModel.sameWorld D (LatentGammaInteger.model D n))
        (Product.owns O (owns O n) left right) left right hleft hright
    iapply hsum.wp v s precision F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [owns]
      iexists left, right
      iexact Hstate
    iexact Hcredit

/-- Compose the unchanged recursive source with its actual exponential constructor spec. -/
theorem integer_latentDistSpec (E : CoPset) (a b : ℤ) (D : Model Ω S) (i : S)
    (O : Val rT → S → IProp GF)
    (hExp : IsLatentDistSpec E pl(&Occil.PSRN.newExponential #a #b #()) D i O) (n : ℕ) :
    IsLatentDistSpec E pl(&Occil.PSRN.newGammaInteger #int ((n + 1 : ℕ) : ℤ) #a #b)
      (LatentGammaInteger.model D n) (LatentGammaInteger.initial i n) (owns O n) := by
  induction n with
  | zero =>
    refine ⟨oracleSpec E D O hExp.oracle 0, ?_⟩
    intro F hF
    rw [Program.source_eq_code]
    iintro Hcredit
    iterate 6 twp_pure
    twp_bind pl(&Occil.PSRN.newExponential #a #b #())
    isimp only [LatentGammaInteger.model, LatentGammaInteger.initial] at Hcredit
    iapply hExp.wp F hF _ $$ Hcredit
    iintro %v %s %hs Hstate Hcredit
    twp_pures
    iapply (tglWp_value_of_toVal (Val.toVal?_fst v))
    isimp only [LatentGammaInteger.model, LatentGammaInteger.initial, owns]
    iexists s
    isplit
    · ipureintro
      exact hs
    iframe Hstate Hcredit
  | succ n IH =>
    refine ⟨oracleSpec E D O hExp.oracle (n + 1), ?_⟩
    intro F hF
    rw [Program.source_eq_code]
    iintro Hcredit
    iterate 6 twp_pure
    twp_bind pl(&Occil.PSRN.newExponential #a #b #())
    isimp only [LatentGammaInteger.model, LatentGammaInteger.initial, Model.add,
      ProductModel.left, ProductModel.expectation_left D (LatentGammaInteger.model D n)
        (i, LatentGammaInteger.initial i n) F hF] at Hcredit
    iapply hExp.wp (ProductModel.leftCredit (LatentGammaInteger.model D n)
      (LatentGammaInteger.initial i n) F)
      (ProductModel.measurable_leftCredit (LatentGammaInteger.model D n)
        (LatentGammaInteger.initial i n) hF) _ $$ Hcredit
    iintro %left %s %hs Hleft Hcredit
    iterate 4 twp_pure
    ieval (change _ ⊢ tglWp E (Program.recursiveBranch n a b left) _)
    rw [Program.recursiveBranch_eq]
    unfold Program.addNext
    twp_bind pl(&Program.gammaCode #int ((n + 1 : ℕ) : ℤ) #a #b)
    rw [Program.source_eq_code] at IH
    isimp only [← ProductModel.expectation_left D (LatentGammaInteger.model D n)
      (s, LatentGammaInteger.initial i n) F hF,
      ProductModel.expectation_right D (LatentGammaInteger.model D n)
        (s, LatentGammaInteger.initial i n) F hF] at Hcredit
    iapply IH.wp (ProductModel.rightCredit D s F) (ProductModel.measurable_rightCredit D s hF) _
      $$ Hcredit
    iintro %right %t %ht Hright Hcredit
    isimp only [Exp.ofVal]
    isimp only [← ProductModel.expectation_right D (LatentGammaInteger.model D n) (s, t) F hF]
      at Hcredit
    iapply tglWp_wand
    isplitl [Hleft Hright]
    · iapply twp_add E left right (Product.owns O (owns O n) left right) (s, t)
      isimp only [Product.owns]
      iframe Hleft Hright
    iintro %v Hstate
    iexists (s, t)
    isplit
    · ipureintro
      exact ⟨hs, ht⟩
    isplitl [Hstate]
    · isimp only [owns]
      iexists left, right
      iexact Hstate
    isimp only [LatentGammaInteger.model, Model.add, ProductModel.left]
    iframe Hcredit

end specification

end

end SampLib.PSRNGammaInteger.Core
