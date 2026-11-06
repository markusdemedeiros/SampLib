import SampLib.Bernoulli.ExpMinusRational
import SampLib.Bernoulli.ReciprocalAffine

/-! # Reciprocal affine exponentials -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ReciprocalExpAffine

noncomputable section

/-- The reciprocal factory applied to an exact rational exponential coin. -/
def bias (a b x y : ℕ) (hb : 0 < b) (hba : b ≤ a) (hy : 0 < y) : unitInterval :=
  ReciprocalAffine.bias
    (ExpMinusRational.bias x y (Int.natCast_nonneg _) (Int.natCast_pos.mpr hy))
    a b b (lt_of_lt_of_le hb hba) hba

/-- The returned probability is `1/(a/b+exp(-x/y))`. -/
theorem coe_bias (a b x y : ℕ) (hb : 0 < b) (hba : b ≤ a) (hy : 0 < y) :
    (bias a b x y hb hba hy : ℝ) =
      1 / ((a : ℝ) / b + Real.exp (-(x : ℝ) / y)) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  simp only [bias, ReciprocalAffine.bias, ExpMinusRational.bias, Int.cast_natCast]
  field_simp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def exponentialCoin (x y : ℕ) : Val rT :=
  ⟨pl(fun u, &Occil.expMinusRational #int (x : ℤ) #int (y : ℤ) #()),
    .lam (by is_lc), by is_lc⟩

private theorem exponentialCoin_spec (E : CoPset) (x y : ℕ) (hy : 0 < y) :
    IsDistSpec (GF := GF) E pl(&(exponentialCoin x y).fst #())
      (RealCoin.law
        (ExpMinusRational.bias x y (Int.natCast_nonneg _) (Int.natCast_pos.mpr hy)))
      Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [ExpMinusRational.expMinusRational_openRec,
      ExpMinusRational.expMinusRational_closeRec]
    iapply (ExpMinusRational.expMinusRational_distSpec E x y (Int.natCast_nonneg _)
      (Int.natCast_pos.mpr hy)).spec F hF $$ Hcredit

/-- Supply the exponential callback to the verified reciprocal affine factory. -/
theorem twp_reciprocalExpAffine (E : CoPset) (a b x y : ℕ)
    (hb : 0 < b) (hba : b ≤ a) (hy : 0 < y) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ r, F r ∂RealCoin.law (bias a b x y hb hba hy)) -∗
      tglWp E pl(&Occil.FactoryExtra.reciprocalExpAffine
        #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
        (fun v : Val rT => iprop(∃ r : Bool, ⌜v = Val.bool r⌝ ∗ ↯ (F r))) := by
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hbound : 1 * b ≤ a * 1 := by simpa using hba
  have hrecip := ReciprocalAffine.reciprocalAffine_distSpec (GF := GF) E
    (ExpMinusRational.bias x y (Int.natCast_nonneg _) (Int.natCast_pos.mpr hy))
    a b 1 1 ha hb (by decide) hbound (exponentialCoin (rT := rT) x y)
    (exponentialCoin_spec E x y hy)
  simp [exponentialCoin, Exp.close, Exp.closeRec] at hrecip
  iintro Hcredit
  iterate 5 twp_pure
  simp only [ReciprocalAffine.reciprocalAffine_openRec,
    ReciprocalAffine.reciprocalAffine_closeRec, ExpMinusRational.expMinusRational_openRec,
    ExpMinusRational.expMinusRational_closeRec]
  isimp only [bias] at Hcredit
  iapply hrecip.spec F (measurable_of_countable _) $$ Hcredit

theorem reciprocalExpAffine_distSpec (E : CoPset) (a b x y : ℕ)
    (hb : 0 < b) (hba : b ≤ a) (hy : 0 < y) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.reciprocalExpAffine
      #int (a : ℤ) #int (b : ℤ) #int (x : ℤ) #int (y : ℤ) #())
      (RealCoin.law (bias a b x y hb hba hy)) Val.bool where
  spec F _ := wand_entails (twp_reciprocalExpAffine E a b x y hb hba hy F)

end specification

end

end SampLib.ReciprocalExpAffine
