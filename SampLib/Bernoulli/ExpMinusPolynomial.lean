import SampLib.Bernoulli.ExpMinusScaled
import SampLib.Bernoulli.CoinProduct
import SampLib.Core.ListEncoding
import SampLib.Core.SamplerStep

/-! # Negative exponentials of polynomials with nonnegative rational coefficients -/

open Set ProbLang
open scoped ENNReal

namespace SampLib.ExpMinusPolynomial

noncomputable section

/-- A nonnegative rational coefficient, represented by a numerator and positive denominator. -/
abbrev Coefficient := {c : ℕ × ℕ // 0 < c.2}

/-- Evaluate the coefficient tail starting at the given degree. -/
def value (p : unitInterval) : List Coefficient → ℕ → ℝ
  | [], _ => 0
  | c :: cs, n => (c.val.1 : ℝ) / c.val.2 * (p : ℝ) ^ n + value p cs (n + 1)

private theorem value_nonneg (p : unitInterval) (cs : List Coefficient) (n : ℕ) :
    0 ≤ value p cs n := by
  induction cs generalizing n with
  | nil => exact le_rfl
  | cons c cs ih =>
    exact add_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (pow_nonneg p.2.1 n)) (ih _)

/-- The probability `exp(-Σᵢ cᵢ pⁱ)`, with the tail beginning at degree `n`. -/
def bias (p : unitInterval) (cs : List Coefficient) (n : ℕ) : unitInterval :=
  ⟨Real.exp (-value p cs n), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (value_nonneg p cs n))⟩

section mathematics

private theorem bias_cons (p : unitInterval) (c : Coefficient) (cs : List Coefficient)
    (n : ℕ) :
    bias p (c :: cs) n = ExpMinusScaled.bias (IterateCoin.bias p n) c.val.1 c.val.2 *
      bias p cs (n + 1) := by
  apply Subtype.ext
  change Real.exp (-value p (c :: cs) n) =
    Real.exp (-(c.val.1 : ℝ) / c.val.2 * (p : ℝ) ^ n) * Real.exp (-value p cs (n + 1))
  rw [← Real.exp_add]
  congr 1
  dsimp [value]
  ring

/-- Each coefficient contributes one independent exponential factor. -/
theorem expectation (p : unitInterval) (c : Coefficient) (cs : List Coefficient)
    (n : ℕ) (F : Bool → ℝ≥0∞) :
    ∫⁻ b, CoinProduct.firstCredit (bias p cs (n + 1)) F b
      ∂RealCoin.law (ExpMinusScaled.bias (IterateCoin.bias p n) c.val.1 c.val.2) =
      ∫⁻ b, F b ∂RealCoin.law (bias p (c :: cs) n) := by
  rw [CoinProduct.expectation_preservation, CoinProduct.law, bias_cons]

end mathematics

private def loopBody {rT : Type _} (coin : Exp rT) (sampler : Val rT) : Exp rT :=
  let trial := pl(&sampler.fst
    &(.lam pl(&Occil.iterateCoin &coin &(.bvar 3)))
    &(Exp.fst (.bvar 0)) &(Exp.snd (.bvar 0)) #())
  let retry := pl(&(.bvar 4) &(Exp.snd (.bvar 1)) (&(.bvar 2) + #1))
  .fix (.lam (.lam (.case (.bvar 1) (.lam pl(#true))
    (.lam (.app (.lam (.cond trial retry pl(#false))) (.fst (.bvar 0)))))))

private def loop {rT : Type _} (coin sampler : Val rT) : Exp rT :=
  loopBody coin.fst sampler

private def program {rT : Type _} (sampler : Val rT) : Exp rT :=
  .lam (.lam (.lam (.app (.lam pl(&(.bvar 0) &(.bvar 2) #0))
    (loopBody (.bvar 8) sampler))))

private def exponentialSampler {rT : Type _} : Val rT :=
  ⟨Occil.FactoryExtra.expMinusScaled, .lam ExpMinusScaled.expMinusScaled_lc,
    ExpMinusScaled.expMinusScaled_lc⟩

private theorem implementation_eq {rT : Type _} :
    program (exponentialSampler : Val rT) = Occil.FactoryExtra.expMinusPolynomial := by
  simp [program, loopBody, exponentialSampler, Occil.FactoryExtra.expMinusPolynomial,
    Exp.close, FactorySyntax.iterateCoin_closeRec, Exp.closeRec]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

def encodeCoefficient (c : Coefficient) : Val rT :=
  .pair (.int c.val.1) (.int c.val.2)

private def powerCoin (coin : Val rT) (n : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.iterateCoin &coin.fst #int (n : ℤ)), .lam (by is_lc), by is_lc⟩

omit [ProbLangDist.IsUniformInt rT] in
private theorem powerCoin_spec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&(powerCoin coin n).fst #())
      (RealCoin.law (IterateCoin.bias p n)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    simp only [FactorySyntax.iterateCoin_openRec]
    iapply (IterateCoin.iterateCoin_distSpec E p coin hcoin n).spec F hF $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_loop (E : CoPset) (p : unitInterval) (coin sampler : Val rT)
    (hsampler : ∀ (n : ℕ) (c : Coefficient),
      IsDistSpec (GF := GF) E pl(&sampler.fst &(powerCoin coin n).fst
        #int (c.val.1 : ℤ) #int (c.val.2 : ℤ) #())
        (RealCoin.law (ExpMinusScaled.bias (IterateCoin.bias p n) c.val.1 c.val.2)) Val.bool)
    (cs : List Coefficient) (n : ℕ) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p cs n)) -∗
      tglWp E pl(&(loop coin sampler) &(listVal encodeCoefficient cs).fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction cs generalizing n with
  | nil =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [bias, value, neg_zero, Real.exp_zero, RealCoin.lintegral_law,
      RealCoin.credit, RealCoin.pmf, sub_self, ENNReal.ofReal_zero, zero_mul,
      ENNReal.ofReal_one, one_mul, add_zero, Bool.false_eq_true, ite_true, ite_false] at Hcredit
    iframe Hcredit
    itrivial
  | cons c cs ih =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    simp only [FactorySyntax.iterateCoin_openRec]
    twp_bind pl(&sampler.fst &(powerCoin coin n).fst
      #int (c.val.1 : ℤ) #int (c.val.2 : ℤ) #())
    isimp only [← expectation p c cs n F] at Hcredit
    iapply ((hsampler n c).wp
      (CoinProduct.firstCredit (bias p cs (n + 1)) F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [CoinProduct.firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · iterate 3 twp_pure
      isimp only [CoinProduct.firstCredit, ite_true] at Hcredit
      have hrec := ih (n + 1)
      simp only [loop, loopBody, Nat.cast_add, Nat.cast_one] at hrec
      isimp only [Exp.ofVal]
      iapply hrec $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_program (E : CoPset) (p : unitInterval) (coin sampler : Val rT)
    (hsampler : ∀ (n : ℕ) (c : Coefficient),
      IsDistSpec (GF := GF) E pl(&sampler.fst &(powerCoin coin n).fst
        #int (c.val.1 : ℤ) #int (c.val.2 : ℤ) #())
        (RealCoin.law (ExpMinusScaled.bias (IterateCoin.bias p n) c.val.1 c.val.2)) Val.bool)
    (cs : List Coefficient) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p cs 0)) -∗
      tglWp E pl(&(program sampler) &coin.fst &(listVal encodeCoefficient cs).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hprogram : (program sampler).IsLocallyClosed := by
    dsimp [program, loopBody]
    is_lc
  iintro Hcredit
  iterate 4
    twp_step
    simp (failIfUnchanged := false) only [loopBody, Exp.open', Exp.openRec, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, FactorySyntax.iterateCoin_openRec, openRec_val_fst]
  have hloop := twp_loop E p coin sampler hsampler cs 0 F
  simp only [loop, loopBody] at hloop
  isimp only [Exp.ofVal, openRec_val_fst]
  iapply hloop $$ Hcredit

/-- Multiply the independent factors while traversing the coefficient list. -/
theorem twp_expMinusPolynomial (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (cs : List Coefficient) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ b, F b ∂RealCoin.law (bias p cs 0)) -∗
      tglWp E pl(&Occil.FactoryExtra.expMinusPolynomial &coin.fst
        &(listVal encodeCoefficient cs).fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  simpa only [implementation_eq] using twp_program E p coin exponentialSampler
    (fun n c => ExpMinusScaled.expMinusScaled_distSpec E (IterateCoin.bias p n)
      c.val.1 c.val.2 c.property (powerCoin coin n) (powerCoin_spec E p coin hcoin n)) cs F

theorem expMinusPolynomial_distSpec (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (cs : List Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.expMinusPolynomial &coin.fst
      &(listVal encodeCoefficient cs).fst #()) (RealCoin.law (bias p cs 0)) Val.bool where
  spec F _ := wand_entails (twp_expMinusPolynomial E p coin hcoin cs F)

end specification

end

end SampLib.ExpMinusPolynomial
