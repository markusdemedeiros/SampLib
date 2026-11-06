import SampLib.LatentMultiplication
import SampLib.LatentAddition
import SampLib.LatentProductModel
import SampLib.Distributions.BetaExponentialProduct
import SampLib.Distributions.GammaErlang

/-! # The independent worlds in the fractional gamma construction

A complementary-shape beta times an independent exponential supplies the fractional
shape. Adding an independent Erlang supplies the integer shape, including zero.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SampLib.LatentGammaFraction

noncomputable section

open LatentReal

variable {ΩI ΩB ΩE SI SB SE : Type}
  [MeasurableSpace ΩI] [MeasurableSpace ΩB] [MeasurableSpace ΩE]

def fraction (B : Model ΩB SB) (E : Model ΩE SE) : Model (ΩB × ΩE) (SB × SE) :=
  (ProductModel.left B E).multiply (ProductModel.right B E) (ProductModel.sameWorld B E)

def model (I : Model ΩI SI) (B : Model ΩB SB) (E : Model ΩE SE) :
    Model (ΩI × (ΩB × ΩE)) (SI × (SB × SE)) :=
  (ProductModel.left I (fraction B E)).add (ProductModel.right I (fraction B E))
    (ProductModel.sameWorld I (fraction B E))

/-- Both multiplication operands belong to one independent product posterior. -/
theorem fraction_law (B : Model ΩB SB) (E : Model ΩE SE) (s : SB × SE) :
    (fraction B E).law s =
      ((B.law s.1).prod (E.law s.2)).map (fun z : ℝ × ℝ => z.1 * z.2) := by
  have hm : Measurable (fun z : ℝ × ℝ => z.1 * z.2) := measurable_fst.mul measurable_snd
  rw [← ProductModel.law_eq_product B E s,
    Measure.map_map hm (B.measurable_value.prodMap E.measurable_value)]
  rfl

/-- The integer and fractional parts retain their complete independent worlds. -/
theorem sum_law (I : Model ΩI SI) (B : Model ΩB SB) (E : Model ΩE SE)
    (s : SI × (SB × SE)) :
    (model I B E).law s =
      ((I.law s.1).prod ((fraction B E).law s.2)).map (fun z : ℝ × ℝ => z.1 + z.2) := by
  have hm : Measurable (fun z : ℝ × ℝ => z.1 + z.2) := measurable_fst.add measurable_snd
  rw [← ProductModel.law_eq_product I (fraction B E) s,
    Measure.map_map hm (I.measurable_value.prodMap (fraction B E).measurable_value)]
  rfl

/-- Beta–exponential multiplication followed by integer gamma addition is canonical gamma. -/
theorem model_law (I : Model ΩI SI) (B : Model ΩB SB) (E : Model ΩE SE)
    (i : SI) (j : SB) (k : SE) (shape rate : ℝ) (n : ℕ)
    (hshape : 0 < shape) (hshape1 : shape < 1) (hrate : 0 < rate)
    (hI : I.law i = GammaErlang.law rate n)
    (hB : B.law j = betaMeasure shape (1 - shape))
    (hE : E.law k = expMeasure rate) :
    (model I B E).law (i, j, k) = gammaMeasure (shape + n) rate := by
  let := GammaErlang.probability rate hrate n
  let := isProbabilityMeasure_gammaMeasure hshape hrate
  rw [sum_law, fraction_law, hI, hB, hE,
    BetaExponentialProduct.beta_mul_exponential shape rate hshape hshape1 hrate]
  change Measure.conv (GammaErlang.law rate n) (gammaMeasure shape rate) = _
  rw [Measure.conv_comm, GammaErlang.gamma_conv_erlang shape rate hshape hrate n]

end

end SampLib.LatentGammaFraction
