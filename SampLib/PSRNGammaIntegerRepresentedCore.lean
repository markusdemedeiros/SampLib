import SampLib.PSRNGammaIntegerCore
import SampLib.LatentRepresentedProduct
import SampLib.LatentRepresentedAddition

/-! # Deterministic interval schedules for the integer-gamma sum

Each observation adds the actual component intervals at the requested precision.
This extends the owned sampler protocol without changing its constructor proof.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGammaInteger.Represented

noncomputable section

open LatentReal

variable {Ω S : Type} [MeasurableSpace Ω]

def representation (D : Model Ω S) (R : Representation D) :
    (n : ℕ) → Representation (LatentGammaInteger.model D n)
  | 0 => R
  | n + 1 => Representation.add _ _
      (ProductModel.sameWorld D (LatentGammaInteger.model D n))
      (Representation.productLeft D (LatentGammaInteger.model D n) R)
      (Representation.productRight D (LatentGammaInteger.model D n) (representation D R n))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Every read certifies its actual sum interval while retaining all component resources. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (O : Val rT → S → IProp GF) (hO : IsRepresentedOracleSpec E D R O) (n : ℕ) :
    IsRepresentedOracleSpec E (LatentGammaInteger.model D n) (representation D R n)
      (Core.owns O n) := by
  induction n with
  | zero => exact hO
  | succ n IH =>
    refine ⟨?_⟩
    intro v s precision F hF
    iintro ⟨Hstate, Hcredit⟩
    isimp only [Core.owns] at Hstate
    icases Hstate with ⟨%left, %right, Hstate⟩
    have hleft := Product.left_representedViewSpec E D (LatentGammaInteger.model D n) R
      O (Core.owns O n) hO left right
    have hright := Product.right_representedViewSpec E D (LatentGammaInteger.model D n)
      (representation D R n) O (Core.owns O n) IH left right
    have hsum : IsRepresentedOracleSpec E (LatentGammaInteger.model D (n + 1))
        (representation D R (n + 1))
        (ViewOwns (addVal left right) (Product.owns O (Core.owns O n) left right)) :=
      represented_add_oracleSpec E _ _
        (ProductModel.sameWorld D (LatentGammaInteger.model D n)) _ _
        (Product.owns O (Core.owns O n) left right) left right hleft hright
    iapply IsRepresentedOracleSpec.wp hsum v s precision F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [Core.owns]
      iexists left, right
      iexact Hstate
    iexact Hcredit

/-- The unchanged constructor and its deterministic represented observations compose together. -/
theorem integer_representedDistSpec (E : CoPset) (a b : ℤ) (D : Model Ω S)
    (R : Representation D) (i : S) (O : Val rT → S → IProp GF)
    (hExp : IsRepresentedDistSpec E pl(&Occil.PSRN.newExponential #a #b #()) D R i O) (n : ℕ) :
    IsRepresentedDistSpec E pl(&Occil.PSRN.newGammaInteger #int ((n + 1 : ℕ) : ℤ) #a #b)
      (LatentGammaInteger.model D n) (representation D R n) (LatentGammaInteger.initial i n)
      (Core.owns O n) where
  toIsLatentPayloadSpec :=
    (Core.integer_latentDistSpec E a b D i O hExp.forget n).payloadSpec
  oracle := oracleSpec E D R O hExp.oracle n

end specification

end

end SampLib.PSRNGammaInteger.Represented
