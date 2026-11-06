import SampLib.PSRN.Support.LatentMultiplication
import SampLib.PSRN.Support.LatentAddition
import SampLib.PSRN.Support.LatentRationalTranslate

open ProbLang SampLib.LatentReal
open scoped ENNReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (E : CoPset) (Dleft Dright : Model Ω S) (hworld : Dleft.SameWorld Dright)
    (P : S → IProp GF) (left right : Val rT)
    (hleft : IsViewSpec E Dleft P left) (hright : IsViewSpec E Dright P right)
    (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ P s ∗ R ∗ ↯ (∫⁻ x, F x ∂(Dleft.add Dright hworld).posterior s) -∗
      tglWp E pl(&(addVal left right).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ (u : S) (I : RationalInterval),
          ⌜v = intervalVal I ∧ Dleft.refines s u ∧
            (Dleft.add Dright hworld).Encloses u n I⌝ ∗
          P u ∗ R ∗ ↯ (∫⁻ x, F x ∂(Dleft.add Dright hworld).posterior u))) := by
  have hsum : IsViewSpec E (Dleft.add Dright hworld) P (addVal left right) :=
    add_oracleSpec E Dleft Dright hworld P left right hleft hright
  iintro ⟨Hstate, HR, Hcredit⟩
  iapply hsum.wp s n F hF _ $$ Hstate Hcredit
  iintro %u %I %hI Hstate Hcredit
  iexists u, I
  iframe Hstate HR Hcredit
  ipureintro
  exact ⟨rfl, hI⟩

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF) (handle : Val rT)
    (h : IsViewSpec E D P handle) :
    IsOracleSpec E (D.add D (Model.SameWorld.refl D))
      (ViewOwns (addVal handle handle) P) :=
  add_oracleSpec E D D (Model.SameWorld.refl D) P handle handle h h

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF) (handle : Val rT)
    (h : IsViewSpec E D P handle) :
    IsOracleSpec E (D.multiply D (Model.SameWorld.refl D))
      (ViewOwns (multiplyVal handle handle) P) :=
  multiply_oracleSpec E D D (Model.SameWorld.refl D) P handle handle h h

#print axioms SampLib.LatentReal.translate_latentDistSpec
#print axioms SampLib.LatentReal.IsViewSpec.wp
#print axioms SampLib.LatentReal.add_oracleSpec

#print axioms SampLib.LatentReal.multiply_oracleSpec
