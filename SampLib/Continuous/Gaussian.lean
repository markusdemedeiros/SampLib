import SampLib.Continuous.GaussianInteger
import SampLib.Continuous.GaussianSelector
import SampLib.Uniform.FairCoin

/-! # Karney's exact standard Gaussian sampler

The Gaussian integer and decreasing-chain selector produce a half-normal value.
An independent fair sign completes the standard Gaussian law.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.Gaussian

noncomputable section

open TotalEris.Examples

abbrev law := ProbabilityTheory.gaussianReal 0 1

/-- Integrating the fair sign over the half-normal strips gives the Gaussian law. -/
theorem expectation (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂law = GaussCreditV F := gauss_credit_eq_gaussianReal F hF

private theorem iterateCoin_eq : (Occil.iterateCoin : Exp ℝ) = IterTrial := rfl

private abbrev selector (k : ℕ) (x : ℝ) : Val ℝ :=
  ⟨pl%(fun u, &Occil.gaussianSelector #int (k : ℤ) #real x), .lam (by is_lc), by is_lc⟩

@[pl_fold] private def loop : Exp ℝ := pl%
  rec draw u :=
    let k := &Occil.gaussianInteger #();
    let x := urand;
    if &Occil.iterateCoin (fun u, &Occil.gaussianSelector k x) (k + #1) then
      x + toReal(k) else draw #()

private theorem fair_credit (F : Bool → ℝ≥0∞) :
    ∫⁻ b, F b ∂RealCoin.law VonNeumann.fairBias = FairCoinCreditV F := by
  rw [RealCoin.lintegral_law]
  norm_num [RealCoin.credit, RealCoin.pmf, VonNeumann.fairBias, FairCoinCreditV]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem abstract_selector (k : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    AbstractBernoulli (GF := GF) (selector k x) (γBkx k x) where
  spec := by
    intro E
    iintro %F Hcredit
    twp_pure
    simp only [GaussianSelector.gaussianSelector_openRec,
      GaussianSelector.gaussianSelector_closeRec]
    isimp only [γBkx_credit_eq F k x hx.1] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (GaussianSelector.twp_gaussianSelector E F k x hx) $$ Hcredit
    iintro %v ⟨%b, %hv, Hcredit⟩
    subst v
    iexists b
    iframe Hcredit
    itrivial

private theorem twp_loop (E : CoPset) (F : ℕ → ℝ → ℝ≥0∞)
    (hF : ∀ k, Measurable (F k)) :
    ⊢ ↯ (G2CreditV F) -∗ tglWp E pl(&loop #())
      (fun v : Val ℝ => iprop(∃ (k : ℕ) (x : ℝ),
        ⌜v = Val.real (x + k)⌝ ∗ ↯ (F k x))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε one_lt_G2Factor $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  let c : ℝ≥0∞ := (G2Factor : ℝ≥0∞) * ε
  twp_pure
  twp_pure
  simp only [GaussianInteger.gaussianInteger_openRec, GaussianInteger.gaussianInteger_closeRec]
  twp_bind pl(&Occil.gaussianInteger #())
  icombine Hcredit Hterm as Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (GaussianInteger.twp_gaussianInteger E (G2G1Credit F c))
    isimp only [← G2G1_collapse F hF ε] at Hcredit
    iexact Hcredit
  iintro %v ⟨%k, %hv, Hcredit⟩
  subst v
  twp_pure
  twp_bind pl(urand)
  isimp only [G2G1Credit] at Hcredit
  iapply (twp_urand_exp (ε₂ := G2CreditAmp F c k) (measurable_g2CreditAmp F hF c k)
    ?_) $$ Hcredit
  · exact le_rfl
  iintro %x ⟨%hx, Hcredit⟩
  have hx' := mem_unifUnitSupport_real_le hx
  twp_pure
  simp only [GaussianSelector.gaussianSelector_openRec, GaussianSelector.gaussianSelector_closeRec]
  twp_bind pl(&Occil.iterateCoin &(selector k x).fst (#int (k : ℤ) + #1))
  twp_pure
  rw [← Nat.cast_add_one, iterateCoin_eq]
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ b : Bool,
    ⌜v.fst = pl(#b)⌝ ∗ ↯ (G2IterContAmp F c k x b) ∗ ⌜True⌝)))
  isplitl [Hcredit]
  · isimp only [G2CreditAmp] at Hcredit
    iapply (twp_IterTrial E (selector k x) (γBkx k x) (iprop(⌜True⌝))
      ((abstract_selector k x hx').toAbstractBernoulliI (iprop(⌜True⌝)))
      (G2IterContAmp F c k x) (k + 1))
    iframe Hcredit
  iintro %v ⟨%b, %hv, Hcredit, -⟩
  obtain rfl : v = Val.bool b := Val.ext hv
  cases b
  · isimp only [G2IterContAmp, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&loop #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists k, x
    isimp only [G2IterContAmp, ite_true] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)

theorem twp_gaussian (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (GaussCreditV F) -∗ tglWp E pl(&Occil.gaussian #())
      (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z))) := by
  iintro Hcredit
  isimp only [GaussCreditV] at Hcredit
  twp_pure
  twp_pure
  simp only [GaussianInteger.gaussianInteger_openRec, GaussianInteger.gaussianInteger_closeRec,
    GaussianSelector.gaussianSelector_openRec, GaussianSelector.gaussianSelector_closeRec]
  twp_bind pl(&loop #())
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (twp_loop E (GaussCredit F) (measurable_gaussCredit hF)) $$ Hcredit
  iintro %v ⟨%k, %x, %hv, Hcredit⟩
  subst v
  twp_pure
  twp_bind pl(&Occil.fairCoin #())
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (FairCoin.twp_fairCoin E (fun b => F (GaussSign (x + k) b)))
    rw [fair_credit]
    isimp only [GaussCredit_eq] at Hcredit
    iexact Hcredit
  iintro %v ⟨%b, %hv, Hcredit⟩
  subst v
  cases b
  · twp_pures
    twp_value
    imodintro
    iexists x + k
    isimp only [GaussSign] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    twp_value
    imodintro
    iexists -(x + k)
    isimp only [GaussSign] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp)

theorem gaussian_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.gaussian #()) law Val.real where
  spec F hF := by
    simpa only [expectation F hF] using wand_entails (twp_gaussian E F hF)

end specification

end

end SampLib.Gaussian
