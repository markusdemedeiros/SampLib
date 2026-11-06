import SampLib.Samplers.ExpHalfCoin

/-! # Karney's nonnegative Gaussian integer

A geometric proposal with bias `exp (-1/2)` is accepted with probability
`exp (-k(k-1)/2)`. Multiplying these factors gives the mass `exp (-k²/2)`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.GaussianInteger

noncomputable section

open TotalEris.Examples

section mathematics

open MeasureTheory

/-- Normalized masses proportional to `exp (-k²/2)` on the natural numbers. -/
def law : Measure ℕ := Measure.sum (fun k => G1PMF k • Measure.dirac k)

instance : IsProbabilityMeasure law where
  measure_univ := by simpa [law, Measure.sum_apply] using G1PMF_tsum

theorem lintegral_law (F : ℕ → ℝ≥0∞) : ∫⁻ k, F k ∂law = G1CreditV F := by
  simp [law, lintegral_sum_measure, lintegral_smul_measure, G1CreditV]

/-- The geometric proposal and its acceptance test preserve Gaussian credit. -/
theorem expectation (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    shiftGeometricPMFCreditV γBNE 0
      (G1GeometricCredit F ((G1Factor : ℝ≥0∞) * ε)) = G1CreditV F + ε :=
  G1Geometric_collapse F ε

end mathematics

theorem gaussianInteger_lc : (Occil.gaussianInteger : Exp ℝ).IsLocallyClosed := by is_lc

theorem gaussianInteger_fv : (Occil.gaussianInteger : Exp ℝ).fv = ∅ := by
  simp [Occil.gaussianInteger, Occil.geometricFailures, Occil.iterateCoin, Exp.fv,
    ExpHalfCoin.expHalfCoin_fv]

@[simp] theorem gaussianInteger_openRec (k : ℕ) (e : Exp ℝ) :
    Exp.openRec k e Occil.gaussianInteger = Occil.gaussianInteger :=
  (Exp.open_lc k e _ gaussianInteger_lc).symm

@[simp] theorem gaussianInteger_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.gaussianInteger : Exp ℝ) = Occil.gaussianInteger :=
  Exp.closeRec_fresh x _ k (by simp [gaussianInteger_fv])

private theorem half_credit (F : Bool → ℝ≥0∞) :
    ENNReal.ofReal (γBNE : ℝ) * F true +
      (1 - ENNReal.ofReal (γBNE : ℝ)) * F false = RealCoin.credit γBNE F := by
  simp [RealCoin.credit, RealCoin.pmf, ENNReal.one_sub_ofReal γBNE_nonneg]

private theorem geometricFailures_eq {rT : Type _} :
    (Occil.geometricFailures : Exp rT) = GeometricTrial := rfl

private theorem iterateCoin_eq {rT : Type _} :
    (Occil.iterateCoin : Exp rT) = IterTrial := rfl

private abbrev halfCoin : Val ℝ :=
  ⟨Occil.expHalfCoin, .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem abstract_halfCoin : AbstractBernoulli (GF := GF) halfCoin γBNE where
  spec := by
    intro E
    iintro %F Hcredit
    isimp only [half_credit] at Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (ExpHalfCoin.twp_expHalfCoin E F) $$ Hcredit
    iintro %v ⟨%b, %hv, Hcredit⟩
    subst v
    iexists b
    iframe Hcredit
    itrivial

theorem twp_gaussianInteger (E : CoPset) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (G1CreditV F) -∗ tglWp E pl(&Occil.gaussianInteger #())
      (fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε one_lt_G1Factor $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  let c : ℝ≥0∞ := (G1Factor : ℝ≥0∞) * ε
  twp_pure
  twp_pure
  twp_bind pl(&Occil.geometricFailures &Occil.expHalfCoin #0)
  icombine Hcredit Hterm as Hcredit
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ z : ℤ,
    ⌜v.fst = pl(#z)⌝ ∗ ⌜0 ≤ z⌝ ∗ ↯ (G1GeometricCredit F c z))))
  isplitl [Hcredit]
  · rw [geometricFailures_eq]
    iapply (twp_GeometricTrial E 0 halfCoin γBNE_pos γBNE_lt_one abstract_halfCoin)
      $$ %(G1GeometricCredit F c)
    isimp only [← expectation F ε] at Hcredit
    iexact Hcredit
  iintro %v ⟨%z, %hv, %hz, Hcredit⟩
  obtain rfl : v = Val.int z := Val.ext hv
  twp_pure
  twp_bind pl(&Occil.iterateCoin &Occil.expHalfCoin (#z * (#z - #1)))
  twp_pure
  twp_pure
  rw [IterN_toNat_cast hz, iterateCoin_eq]
  iapply (tglWp_wand (Φ := fun v : Val ℝ => iprop(∃ b : Bool,
    ⌜v.fst = pl(#b)⌝ ∗ ↯ (G1IterContAmp F c z.toNat b) ∗ ⌜True⌝)))
  isplitl [Hcredit]
  · isimp only [G1GeometricCredit] at Hcredit
    iapply (twp_IterTrial E halfCoin γBNE (iprop(⌜True⌝))
      (abstract_halfCoin.toAbstractBernoulliI (iprop(⌜True⌝)))
      (G1IterContAmp F c z.toNat) (IterN z.toNat))
    iframe Hcredit
  iintro %v ⟨%b, %hv, Hcredit, -⟩
  obtain rfl : v = Val.bool b := Val.ext hv
  cases b
  · isimp only [G1IterContAmp, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_bind pl(&Occil.gaussianInteger #())
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply IH $$ Hterm Hcredit
  · twp_pures
    twp_value
    imodintro
    iexists z.toNat
    isimp only [G1IterContAmp, ite_true] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext (by simp [Int.toNat_of_nonneg hz])

theorem gaussianInteger_distSpec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.gaussianInteger #()) law
      (fun k : ℕ => Val.int k) where
  spec F _ := by
    simpa only [lintegral_law] using wand_entails (twp_gaussianInteger E F)

end specification

end

end SampLib.GaussianInteger
