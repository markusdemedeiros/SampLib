import SampLib.Latent.LatentUniform
import SampLib.PSRN.Support.LatentRational
import SampLib.PSRN.Support.LatentProduct
import SampLib.PSRN.Support.LatentAddition
import SampLib.Continuous.UniformSum
import SampLib.PSRN.Syntax.PSRNUniformSum

/-! # Deferred Irwin–Hall sampling

Independent uniform constructors allocate one shared product world. Every later
sum observation retains that world and all its cached component digits.
-/

open ProbLang
open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.PSRNUniformSum

open scoped SampLib.PSRNUniformSum

noncomputable section

open LatentReal

/-- One latent unit uniform per summand; zero summands require no randomness. -/
abbrev World : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × World n

instance worldMeasurableSpace : (n : ℕ) → MeasurableSpace (World n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => (inferInstance : MeasurableSpace ℝ).prod (worldMeasurableSpace n)

/-- Each uniform retains its current cached prefix. -/
abbrev State : ℕ → Type
  | 0 => Unit
  | n + 1 => List Bool × State n

def model : (n : ℕ) → Model (World n) (State n)
  | 0 => LatentRational.model 0 1
  | n + 1 =>
    (ProductModel.left LatentUniform.model (model n)).add
      (ProductModel.right LatentUniform.model (model n))
      (ProductModel.sameWorld LatentUniform.model (model n))

def initial : (n : ℕ) → State n
  | 0 => ()
  | n + 1 => ([], initial n)

section mathematics

open MeasureTheory

/-- Independent component laws push forward by addition. -/
theorem sum_law {Ω₁ Ω₂ S₁ S₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (L : Model Ω₁ S₁) (R : Model Ω₂ S₂) (s : S₁ × S₂) :
    ((ProductModel.left L R).add (ProductModel.right L R) (ProductModel.sameWorld L R)).law s =
      ((L.law s.1).prod (R.law s.2)).map (fun z : ℝ × ℝ => z.1 + z.2) := by
  have hsum : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
  have hpair : Measurable (Prod.map L.value R.value) :=
    L.measurable_value.prodMap R.measurable_value
  rw [← ProductModel.law_eq_product L R s, Measure.map_map hsum hpair]
  rfl

/-- The latent sum has exactly the same Irwin–Hall law as the eager real sampler. -/
theorem model_law (n : ℕ) : (model n).law (initial n) = UniformSum.law n := by
  induction n with
  | zero => simp [model, initial, LatentRational.model_law, UniformSum.law]
  | succ n ih =>
    rw [model, initial, sum_law, ih, UniformSum.law]
    congr 2
    change (DyadicPosterior.law []).map id = LawfulProbLangℝ.unifUnit (T := ℝ)
    rw [Measure.map_id, DyadicPosterior.law_nil]
    exact restrict_Ico_eq_restrict_Icc

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A nested sum owns its actual constituent handles once each. -/
def owns : (n : ℕ) → Val rT → State n → IProp GF
  | 0 => LatentRational.owns 0 1
  | n + 1 => fun v s => iprop(∃ (left right : Val rT),
    ViewOwns (addVal left right) (Product.owns LatentUniform.owns (owns n) left right) v s)

/-- Every sum read preserves the full joint latent credit and all allocated caches. -/
theorem oracleSpec (E : CoPset) (n : ℕ) :
    IsOracleSpec (GF := GF) E (model n) (owns n) := by
  induction n with
  | zero => exact LatentRational.oracleSpec (rT := rT) (GF := GF) E 0 1 (by decide)
  | succ n ih =>
    refine ⟨?_⟩
    intro v s precision F hF
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%left, %right, Hstate⟩
    have hleft := Product.left_viewSpec (rT := rT) (GF := GF) E LatentUniform.model (model n)
      LatentUniform.owns (owns n) (LatentUniform.oracleSpec (rT := rT) (GF := GF) E) left right
    have hright := Product.right_viewSpec (rT := rT) (GF := GF) E LatentUniform.model (model n)
      LatentUniform.owns (owns n) ih left right
    have hsum : IsOracleSpec (GF := GF) E (model (n + 1))
        (ViewOwns (addVal left right)
          (Product.owns LatentUniform.owns (owns n) left right)) :=
      add_oracleSpec (rT := rT) (GF := GF) E _ _
        (ProductModel.sameWorld LatentUniform.model (model n))
        (Product.owns LatentUniform.owns (owns n) left right) left right hleft hright
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

/-- The actual recursive constructor yields an observable deferred Irwin–Hall draw. -/
theorem newUniformSum_latentDistSpec (E : CoPset) (n : ℕ) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newUniformSum #int (n : ℤ))
      (model n) (initial n) (owns n) := by
  induction n with
  | zero =>
    refine ⟨oracleSpec E 0, ?_⟩
    intro F hF
    iintro Hcredit
    iterate 6 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    have hbase : IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.rational #0 #1)
        (model 0) (initial 0) (owns 0) :=
      LatentRational.rational_latentDistSpec (rT := rT) (GF := GF) E 0 1 (by decide)
    iapply hbase.spec F hF $$ Hcredit
  | succ n ih =>
    refine ⟨oracleSpec E (n + 1), ?_⟩
    intro F hF
    iintro Hcredit
    iterate 6 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_bind pl(&Occil.PSRN.newUniform #())
    isimp only [model, initial, Model.add, ProductModel.left,
      ProductModel.expectation_left LatentUniform.model (model n) ([], initial n) F hF]
      at Hcredit
    iapply (LatentUniform.newUniform_latentDistSpec (rT := rT) (GF := GF) E).wp
      (ProductModel.leftCredit (model n) (initial n) F)
      (ProductModel.measurable_leftCredit (model n) (initial n) hF) _ $$ Hcredit
    iintro %left %s %hs Hleft Hcredit
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    simp only [ClosedExp.openRec]
    twp_bind pl(&sumCode #int (n : ℤ))
    rw [source_eq_code] at ih
    isimp only [← ProductModel.expectation_left LatentUniform.model (model n)
      (s, initial n) F hF, ProductModel.expectation_right LatentUniform.model (model n)
      (s, initial n) F hF] at Hcredit
    iapply ih.wp (ProductModel.rightCredit LatentUniform.model s F)
      (ProductModel.measurable_rightCredit LatentUniform.model s hF) _ $$ Hcredit
    iintro %right %t %ht Hright Hcredit
    twp_pures
    twp_value
    imodintro
    isimp only [← ProductModel.expectation_right LatentUniform.model (model n) (s, t) F hF]
      at Hcredit
    iexists (s, t)
    isplit
    · ipureintro
      exact ⟨hs, ht⟩
    isplitl [Hleft Hright]
    · isimp only [owns, ViewOwns, Product.owns]
      iexists left, right
      iframe Hleft Hright
      ipureintro
      rfl
    isimp only [model, Model.add, ProductModel.left]
    iframe Hcredit

end specification

end

end SampLib.PSRNUniformSum
