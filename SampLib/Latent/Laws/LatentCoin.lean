module

public import SampLib.Latent.Laws.Model
public import SampLib.Uniform.Laws.RealCoin

@[expose] public section

/-! # Credit kernel of a coin conditioned on a latent world

The kernel keeps both the returned bit and the whole latent state, so a second coin on the
same world never assumes independence of the two marginals.
-/

open MeasureTheory (Measure IsProbabilityMeasure)
open scoped ENNReal

namespace SampLib.LatentReal

noncomputable section

namespace LatentCoin

section mathematics

open MeasureTheory

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Conditional expected continuation credit for one coin call. -/
def kernel (bias : Ω → unitInterval) (G : Bool → Ω → ℝ≥0∞) (x : Ω) : ℝ≥0∞ :=
  RealCoin.credit (bias x) (fun b => G b x)

/-- All dependencies on the latent world remain measurable. -/
theorem measurable_kernel {bias : Ω → unitInterval} (hbias : Measurable bias)
    {G : Bool → Ω → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) :
    Measurable (kernel bias G) := by
  have ht := hG true
  have hf := hG false
  unfold kernel RealCoin.credit RealCoin.pmf
  simp only [ite_true, Bool.false_eq_true, ite_false]
  fun_prop

/-- Expected credit under the source's current joint posterior. -/
def credit (D : Model Ω S) (s : S) (bias : Ω → unitInterval)
    (G : Bool → Ω → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x, kernel bias G x ∂D.posterior s

/-- An independent fixed-bias coin commutes with posterior expectation. -/
theorem credit_fixed_bias (D : Model Ω S) (s : S) (p : unitInterval)
    (G : Bool → Ω → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    credit D s (fun _ => p) G =
      RealCoin.credit p (fun b => ∫⁻ x, G b x ∂D.posterior s) := by
  unfold credit kernel RealCoin.credit RealCoin.pmf
  simp only [ite_true, Bool.false_eq_true, ite_false]
  have ht : Measurable (fun x => ENNReal.ofReal (p : ℝ) * G true x) :=
    measurable_const.mul (hG true)
  rw [lintegral_add_left ht _, lintegral_const_mul _ (hG true),
    lintegral_const_mul _ (hG false)]

end mathematics

end LatentCoin

end

end SampLib.LatentReal
