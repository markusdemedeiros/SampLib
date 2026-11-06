import SampLib.LatentGammaFractionModel
import SampLib.LatentProduct
import SampLib.Syntax.PSRNGamma

/-! # The fractional branch of the actual rational-shape gamma constructor

The three constructors allocate independent worlds. Multiplication and addition
then capture their handles without observing or duplicating any source state.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGamma.Core

noncomputable section

open LatentReal
open scoped SampLib.PSRNGamma.Program SampLib.PSRNGammaInteger.Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {ΩI ΩB ΩE SI SB SE : Type}
  [MeasurableSpace ΩI] [MeasurableSpace ΩB] [MeasurableSpace ΩE]
local bi (IProp GF)

/-- The fractional handle owns the independent beta and exponential handles. -/
def fractionOwns (OB : Val rT → SB → IProp GF) (OE : Val rT → SE → IProp GF)
    (v : Val rT) (s : SB × SE) : IProp GF :=
  iprop(∃ (beta exponential : Val rT),
    ViewOwns (multiplyVal beta exponential) (Product.owns OB OE beta exponential) v s)

/-- The sum retains the entire integer, beta and exponential state. -/
def owns (OI : Val rT → SI → IProp GF) (OB : Val rT → SB → IProp GF)
    (OE : Val rT → SE → IProp GF) (v : Val rT) (s : SI × (SB × SE)) : IProp GF :=
  iprop(∃ (integer fractional : Val rT),
    ViewOwns (addVal integer fractional)
      (Product.owns OI (fractionOwns OB OE) integer fractional) v s)

theorem fraction_oracleSpec (E : CoPset) (B : Model ΩB SB) (X : Model ΩE SE)
    (OB : Val rT → SB → IProp GF) (OE : Val rT → SE → IProp GF)
    (hB : IsOracleSpec E B OB) (hE : IsOracleSpec E X OE) :
    IsOracleSpec E (LatentGammaFraction.fraction B X) (fractionOwns OB OE) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [fractionOwns] at Hstate
    icases Hstate with ⟨%beta, %exponential, Hstate⟩
    have hleft := Product.left_viewSpec E B X OB OE hB beta exponential
    have hright := Product.right_viewSpec E B X OB OE hE beta exponential
    have hmul : IsOracleSpec E (LatentGammaFraction.fraction B X)
        (ViewOwns (multiplyVal beta exponential) (Product.owns OB OE beta exponential)) :=
      multiply_oracleSpec E _ _ (ProductModel.sameWorld B X)
      (Product.owns OB OE beta exponential) beta exponential hleft hright
    iapply hmul.wp v s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [fractionOwns]
      iexists beta, exponential
      iexact Hstate
    iexact Hcredit

theorem oracleSpec (E : CoPset) (I : Model ΩI SI) (B : Model ΩB SB) (X : Model ΩE SE)
    (OI : Val rT → SI → IProp GF) (OB : Val rT → SB → IProp GF)
    (OE : Val rT → SE → IProp GF) (hI : IsOracleSpec E I OI)
    (hB : IsOracleSpec E B OB) (hE : IsOracleSpec E X OE) :
    IsOracleSpec E (LatentGammaFraction.model I B X) (owns OI OB OE) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%integer, %fractional, Hstate⟩
    have hf := fraction_oracleSpec E B X OB OE hB hE
    have hleft := Product.left_viewSpec E I (LatentGammaFraction.fraction B X)
      OI (fractionOwns OB OE) hI integer fractional
    have hright := Product.right_viewSpec E I (LatentGammaFraction.fraction B X)
      OI (fractionOwns OB OE) hf integer fractional
    have hsum : IsOracleSpec E (LatentGammaFraction.model I B X)
        (ViewOwns (addVal integer fractional)
          (Product.owns OI (fractionOwns OB OE) integer fractional)) :=
      add_oracleSpec E _ _
      (ProductModel.sameWorld I (LatentGammaFraction.fraction B X))
      (Product.owns OI (fractionOwns OB OE) integer fractional) integer fractional hleft hright
    iapply hsum.wp v s n F hF _ $$ Hstate Hcredit
    iintro %t %J %hJ Hstate Hcredit
    iexists t, J
    isplit
    · ipureintro
      exact ⟨rfl, hJ⟩
    isplitl [Hstate]
    · isimp only [owns]
      iexists integer, fractional
      iexact Hstate
    iexact Hcredit

private theorem beta_beta (E : CoPset) (a b : ℤ) (integer beta : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E (Program.bind (Program.exponential a b) (Program.afterExponential integer beta)) Φ ⊢
      tglWp E (.app (.lam (Program.afterBeta a b integer)) beta.fst) Φ := by
  rw [← Program.opened_afterBeta]
  exact twp_beta E [] _ beta (Program.afterBeta_lc a b integer) Φ

private theorem exponential_beta (E : CoPset) (integer beta exponential : Val rT)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&Occil.PSRN.add &integer.fst
      (&Occil.PSRN.multiply &beta.fst &exponential.fst)) Φ ⊢
      tglWp E (.app (.lam (Program.afterExponential integer beta)) exponential.fst) Φ := by
  rw [← Program.opened_afterExponential]
  exact twp_beta E [] _ exponential (Program.afterExponential_lc integer beta) Φ

/-- After the integer part, the literal fractional branch constructs the beta and
exponential factors and returns the sum, retaining all three component caches. -/
theorem twp_fraction (E : CoPset) (r d a b : ℤ)
    (I : Model ΩI SI) (B : Model ΩB SB) (X : Model ΩE SE) (i : SI) (j : SB) (k : SE)
    (OI : Val rT → SI → IProp GF) (OB : Val rT → SB → IProp GF)
    (OE : Val rT → SE → IProp GF)
    (hB : IsLatentDistSpec E (Program.beta r d) B j OB)
    (hE : IsLatentDistSpec E (Program.exponential a b) X k OE)
    (iv : Val rT) (s : SI) (hs : I.refines i s) (F : ΩI × (ΩB × ΩE) → ℝ≥0∞)
    (hF : Measurable F) :
    iprop(OI iv s ∗ ↯ (∫⁻ x, F x ∂(LatentGammaFraction.model I B X).posterior (s, j, k))) ⊢
      tglWp E (Program.bind (Program.beta r d) (Program.afterBeta a b iv))
        (fun v : Val rT => iprop(∃ t, ⌜(LatentGammaFraction.model I B X).refines (i, j, k) t⌝ ∗
          owns OI OB OE v t ∗ ↯ (∫⁻ x, F x ∂(LatentGammaFraction.model I B X).posterior t))) := by
  iintro ⟨HI, Hcredit⟩
  unfold Program.bind
  twp_bind (Program.beta r d)
  let G := ProductModel.rightCredit I s F
  have hG : Measurable G := ProductModel.measurable_rightCredit I s hF
  have hsplit : ∫⁻ y, G y ∂(LatentGammaFraction.fraction B X).posterior (j, k) ≤
      ∫⁻ x, F x ∂(LatentGammaFraction.model I B X).posterior (s, j, k) :=
    (ProductModel.expectation_right I (LatentGammaFraction.fraction B X) (s, j, k) F hF).ge
  have hleft : ∫⁻ x, ProductModel.leftCredit X k G x ∂B.posterior j ≤
      ∫⁻ y, G y ∂(LatentGammaFraction.fraction B X).posterior (j, k) :=
    (ProductModel.expectation_left B X (j, k) G hG).ge
  ihave Hcredit := ErrorCredit.weaken (hleft.trans hsplit) $$ Hcredit
  iapply hB.wp (ProductModel.leftCredit X k G)
    (ProductModel.measurable_leftCredit X k hG) _ $$ Hcredit
  iintro %bv %t %ht HB Hcredit
  isimp only [Exp.ofVal]
  iapply beta_beta E a b iv bv _
  unfold Program.bind
  twp_bind (Program.exponential a b)
  ihave Hcredit := ErrorCredit.weaken ((ProductModel.expectation_right B X (t, k) G hG).symm.trans
    (ProductModel.expectation_left B X (t, k) G hG)).le $$ Hcredit
  iapply hE.wp (ProductModel.rightCredit B t G)
    (ProductModel.measurable_rightCredit B t hG) _ $$ Hcredit
  iintro %ev %u %hu HE Hcredit
  isimp only [Exp.ofVal]
  iapply exponential_beta E iv bv ev _
  twp_bind pl(&Occil.PSRN.multiply &bv.fst &ev.fst)
  iapply tglWp_wand
  isplitl [HB HE]
  · iapply twp_multiply E bv ev (Product.owns OB OE bv ev) (t, u)
    isimp only [Product.owns]
    iframe HB HE
  iintro %fv HF
  isimp only [Exp.ofVal]
  iapply tglWp_wand
  isplitl [HI HF]
  · iapply twp_add E iv fv (Product.owns OI (fractionOwns OB OE) iv fv) (s, t, u)
    isimp only [Product.owns]
    isplitl [HI]
    · iexact HI
    isimp only [fractionOwns]
    iexists bv, ev
    iexact HF
  iintro %v Hstate
  iexists (s, t, u)
  isplit
  · ipureintro
    exact ⟨hs, ht, hu⟩
  isplitl [Hstate]
  · isimp only [owns]
    iexists iv, fv
    iexact Hstate
  have hsum : ∫⁻ x, F x ∂(LatentGammaFraction.model I B X).posterior (s, t, u) ≤
      ∫⁻ y, ProductModel.rightCredit B t G y ∂X.posterior u :=
    ((ProductModel.expectation_right I (LatentGammaFraction.fraction B X) (s, t, u) F hF).trans
      (ProductModel.expectation_right B X (t, u) G hG)).le
  ihave Hcredit := ErrorCredit.weaken hsum $$ Hcredit
  iexact Hcredit

end specification

end

end SampLib.PSRNGamma.Core
