import SampLib.Distributions.LatentReal.UniformAbove
import SampLib.PSRNLess
import SampLib.LatentProduct
import SampLib.LatentCompositeMeasuredError

/-! # The actual fresh-uniform comparison above an owned source -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.UniformAbove

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- One fresh independent uniform is discarded; all original source credit and ownership remain. -/
theorem twp_above (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (O : Val rT → S → IProp GF) (horacle : IsOracleSpec E D O)
    (source : Val rT) (s : S) (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(O source s ∗ ↯ (LatentCoin.credit D s (bias D) G)) ⊢
      tglWp E pl(&Occil.PSRN.less &source.fst (&Occil.PSRN.newUniform #()))
        (LatentCoin.post D O source s G) := by
  have hallocate : (∫⁻ z, kernel D G z
      ∂ProductModel.posterior LatentUniform.model D ([], s)) =
      DyadicPosterior.credit [] (ProductModel.leftCredit D s (kernel D G)) :=
    ProductModel.expectation_left LatentUniform.model D ([], s) (kernel D G)
      (measurable_kernel D G hG)
  have hkernel : kernel D G =
      Less.outputCredit (ProductModel.right LatentUniform.model D)
        (ProductModel.left LatentUniform.model D) (fun b z => G b z.2) := rfl
  have hworld : (ProductModel.right LatentUniform.model D).SameWorld
      (ProductModel.left LatentUniform.model D) := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
  iintro ⟨Hsource, Hcredit⟩
  isimp only [← expectation D s G hG, hallocate] at Hcredit
  twp_bind pl(&Occil.PSRN.newUniform #())
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply LatentUniform.twp_newUniform E (ProductModel.leftCredit D s (kernel D G)) $$ Hcredit
  iintro %uniform ⟨Huniform, Hcredit⟩
  isimp only [← hallocate] at Hcredit
  isimp only [Exp.ofVal]
  iapply tglWp_wand
  isplitl [Huniform Hsource Hcredit]
  · iapply Less.twp_less E (ProductModel.right LatentUniform.model D)
      (ProductModel.left LatentUniform.model D) hworld
      (Model.MeasurableError.product_right herror)
      (Model.MeasurableError.product_left (fun _ => measurable_const))
      (Product.owns LatentUniform.owns O uniform source) source uniform
      (Product.right_viewSpec E LatentUniform.model D LatentUniform.owns O horacle uniform source)
      (Product.left_viewSpec E LatentUniform.model D LatentUniform.owns O
        (LatentUniform.oracleSpec E) uniform source)
      ([], s) ((UniformThreshold.ae_distinct D s).mono fun _ h => h.symm)
      (fun b z => G b z.2) (fun b => (hG b).comp measurable_snd)
    isimp only [hkernel, ProductModel.right, ProductModel.left] at Hcredit
    isimp only [Product.owns, ProductModel.right, ProductModel.left]
    iframe Huniform Hsource Hcredit
  iintro %result Hpost
  isimp only [Less.post] at Hpost
  icases Hpost with ⟨%b, %t, %ht, Hstate, Hcredit⟩
  isimp only [Product.owns] at Hstate
  icases Hstate with ⟨Huniform, Hsource⟩
  isimp only [ProductModel.right, ProductModel.left,
    UniformThreshold.marginal_credit D t.1 t.2 (G b) (hG b)] at Hcredit
  isimp only [LatentCoin.post]
  iexists b, t.2
  iframe Hsource Hcredit
  ipureintro
  exact ⟨ht.1, ht.2.1.2⟩

/-- The reusable conditional contract retains the same latent world on every comparison. -/
theorem programSpec (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (O : Val rT → S → IProp GF) (horacle : IsOracleSpec E D O) :
    IsLatentCoinProgramSpec E D O (bias D)
      (fun source => pl(&Occil.PSRN.less &source.fst (&Occil.PSRN.newUniform #()))) where
  measurable_bias := measurable_bias D
  spec source s G hG := twp_above E D herror O horacle source s G hG

end

end SampLib.LatentReal.UniformAbove
