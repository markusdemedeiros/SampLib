import SampLib.PSRN.Laws.ProductModel
import SampLib.PSRN.Support.Arithmetic.Addition
import SampLib.Latent.LatentViews
import SampLib.Latent.Laws.MeasuredError
import SampLib.PSRN.Laws.GammaSuccessor
import SampLib.PSRN.Support.Arithmetic.Product
import SampLib.PSRN.Syntax.PSRNGammaInteger

/-! # The positive integer-gamma source from its exponential component

Every recursive step allocates a new independent exponential world, then returns
an addition oracle over the complete product state. Depth `n` means shape `n+1`.
-/

open MeasureTheory
open scoped ENNReal

namespace SampLib.LatentGammaInteger

noncomputable section

open LatentReal

abbrev World (Ω : Type) : ℕ → Type
  | 0 => Ω
  | n + 1 => Ω × World Ω n

instance worldMeasurableSpace (Ω : Type) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (World Ω n)
  | 0 => inferInstanceAs (MeasurableSpace Ω)
  | n + 1 => (inferInstance : MeasurableSpace Ω).prod (worldMeasurableSpace Ω n)

abbrev State (S : Type) : ℕ → Type
  | 0 => S
  | n + 1 => S × State S n

variable {Ω S : Type} [MeasurableSpace Ω]

def model (D : Model Ω S) : (n : ℕ) → Model (World Ω n) (State S n)
  | 0 => D
  | n + 1 =>
    (ProductModel.left D (model D n)).add (ProductModel.right D (model D n))
      (ProductModel.sameWorld D (model D n))

def initial (i : S) : (n : ℕ) → State S n
  | 0 => i
  | n + 1 => (i, initial i n)

private theorem sum_law {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂) :
    ((ProductModel.left L R).add (ProductModel.right L R) (ProductModel.sameWorld L R)).law s =
      ((L.law s.1).prod (R.law s.2)).map (fun z : ℝ × ℝ => z.1 + z.2) := by
  have hsum : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
  rw [← ProductModel.law_eq_product L R s,
    Measure.map_map hsum (L.measurable_value.prodMap R.measurable_value)]
  rfl

/-- The depth-`n` sum has gamma shape `n+1` at the component exponential's rate. -/
theorem model_law (D : Model Ω S) (i : S) (rate : ℝ) (hrate : 0 < rate)
    (hD : D.law i = ProbabilityTheory.expMeasure rate) (n : ℕ) :
    (model D n).law (initial i n) = ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate := by
  induction n with
  | zero => simpa only [model, initial, Nat.zero_add, Nat.cast_one, ProbabilityTheory.expMeasure]
      using hD
  | succ n IH =>
    rw [model, initial, sum_law, hD, IH]
    change Measure.conv (ProbabilityTheory.expMeasure rate)
      (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate) = _
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      GammaSuccessor.exponential_conv_gamma ((n + 1 : ℕ) : ℝ) rate (by positivity) hrate

/-- Finite sums preserve measurable observation errors componentwise. -/
theorem measurable_error (D : Model Ω S) (hD : D.MeasurableError) (n : ℕ) :
    (model D n).MeasurableError := by
  induction n with
  | zero => exact hD
  | succ n IH =>
    intro k
    change Measurable (fun z : Ω × World Ω n => D.error k z.1 + (model D n).error k z.2)
    exact ((hD k).comp measurable_fst).add ((IH k).comp measurable_snd)

end

end SampLib.LatentGammaInteger

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
