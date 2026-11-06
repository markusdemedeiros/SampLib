import SampLib.Uniform.RealCoin
import SampLib.Continuous.Laws.Gaussian
import Samplers.Continuous
import SampLib.Continuous.Laws.GaussianSelector

/-! # Karney's Gaussian acceptance coin

The thinned decreasing chain has parity bias
`exp (-x(2k+x)/(2k+2))`. Its extra stopping coin supplies a uniform termination
bound even when the initial decreasing threshold is one.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.GaussianSelector

noncomputable section

open TotalEris.Examples

theorem gaussianSelector_lc : (Occil.gaussianSelector : Exp ℝ).IsLocallyClosed := by is_lc

theorem gaussianSelector_fv : (Occil.gaussianSelector : Exp ℝ).fv = ∅ := by
  simp [Occil.gaussianSelector, Occil.gaussianSelectorCoin, Occil.gaussianSelectorC, Exp.fv]

@[simp] theorem gaussianSelector_openRec (k : ℕ) (e : Exp ℝ) :
    Exp.openRec k e Occil.gaussianSelector = Occil.gaussianSelector :=
  (Exp.open_lc k e _ gaussianSelector_lc).symm

@[simp] theorem gaussianSelector_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.gaussianSelector : Exp ℝ) = Occil.gaussianSelector :=
  Exp.closeRec_fresh x _ k (by simp [gaussianSelector_fv])

private theorem gaussianSelectorCoin_lc :
    (Occil.gaussianSelectorCoin : Exp ℝ).IsLocallyClosed := by is_lc

private theorem gaussianSelectorCoin_fv : (Occil.gaussianSelectorCoin : Exp ℝ).fv = ∅ := by
  simp [Occil.gaussianSelectorCoin, Occil.gaussianSelectorC, Exp.fv]

@[simp] private theorem gaussianSelectorCoin_openRec (k : ℕ) (e : Exp ℝ) :
    Exp.openRec k e Occil.gaussianSelectorCoin = Occil.gaussianSelectorCoin :=
  (Exp.open_lc k e _ gaussianSelectorCoin_lc).symm

@[simp] private theorem gaussianSelectorCoin_closeRec (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.gaussianSelectorCoin : Exp ℝ) = Occil.gaussianSelectorCoin :=
  Exp.closeRec_fresh x _ k (by simp [gaussianSelectorCoin_fv])

private theorem parity_beq (n : ℕ) :
    ((BaseLit.int ((n : ℤ) % 2) : BaseLit ℝ) == .int 0) = decide (n % 2 = 0) := by
  change ((n : ℤ) % 2 == 0) = decide (n % 2 = 0)
  rw [beq_eq_decide, decide_eq_decide]
  omega

private theorem parity_credit (F : Bool → ℝ≥0∞) (n : ℕ) :
    BS0Credit F n = F (decide (n % 2 = 0)) := by
  by_cases h : n % 2 = 0 <;> simp [BS0Credit, h]

private theorem biiCredit_one (F : Bool → ℝ≥0∞) (x r : ℝ) :
    BiiCredit F x 1 r = F (ProbLangℝ.realLt x r) := by
  by_cases h : x < r <;> simp [BiiCredit, h,
    show ProbLangℝ.realLt x r = decide (x < r) from rfl]

private theorem selectorC_eq {rT : Type _} : (Occil.gaussianSelectorC : Exp rT) = C := rfl

@[pl_fold] private def loop (k : ℕ) (x : ℝ) : Exp ℝ := pl%
  rec trial y n :=
    let z := urand;
    if y < z then n else
      if &Occil.gaussianSelectorCoin #int (k : ℤ) #real x #() then n
      else trial z (n + #1)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

private theorem twp_coin (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢ ↯ (BiiCreditV F k x) -∗
      tglWp E pl(&Occil.gaussianSelectorCoin #int (k : ℤ) #real x #())
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&Occil.gaussianSelectorC (#2 * #int (k : ℤ)))
  twp_pure
  rw [show 2 * (k : ℤ) = ((2 * k : ℕ) : ℤ) by simp]
  iapply tglWp_wand
  isplitl [Hcredit]
  · rw [selectorC_eq]
    iapply (twp_C E (BiiCCredit F x) (2 * k))
    isimp only [biiCreditV_C_eq F k x hx.1 hx.2] at Hcredit
    iexact Hcredit
  iintro %v ⟨%n, %hv, %hn, Hcredit⟩
  obtain rfl : v = Val.int n := Val.ext hv
  twp_pure
  twp_bind pl(urand)
  isimp only [BiiCCredit] at Hcredit
  iapply (twp_urand_exp (ε₂ := BiiCredit F x n) (measurable_biiCredit F x n) ?_) $$ Hcredit
  · exact le_rfl
  iintro %r ⟨_, Hcredit⟩
  twp_pure
  obtain rfl | rfl | rfl := hn
  · twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [BiiCredit, Nat.reduceEqDiff, reduceIte] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    twp_value
    imodintro
    iexists (ProbLangℝ.realLt x r)
    isimp only [biiCredit_one] at Hcredit
    iframe Hcredit
    itrivial
  · twp_pures
    twp_value
    imodintro
    iexists false
    isimp only [BiiCredit, Nat.reduceEqDiff, reduceIte] at Hcredit
    iframe Hcredit
    itrivial

private theorem twp_loop (E : CoPset) (F : ℕ → ℝ≥0∞) (k : ℕ) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (y : ℝ) (hy : 0 ≤ y ∧ y ≤ 1) (n : ℕ) :
    ⊢ ↯ (SCreditV F k x y n) -∗
      tglWp E pl(&(loop k x) #real y #int (n : ℤ))
        (fun v : Val ℝ => iprop(∃ m : ℕ, ⌜v = Val.int m⌝ ∗ ↯ (F m))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %y %hy %n Hcredit
  iapply ErrorCredit.Induction.simple hε (one_lt_factor k) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %y %hy %n Hcredit
  twp_pures
  twp_bind pl(urand)
  icombine Hcredit Hterm as Hcredit
  iapply (twp_urand_exp (ε₂ := SCreditAmp F k x n y (factor k * ε))
    (measurable_sCreditAmp F k x n y _) (expectation F k x y n hx hy ε)) $$ Hcredit
  iintro %z ⟨%hz, Hcredit⟩
  have hz' := mem_unifUnitSupport_real_le hz
  twp_pures
  rcases hyz : ProbLangℝ.realLt y z with _ | _
  · isimp only [SCreditAmp, of_decide_eq_false hyz, reduceIte] at Hcredit
    twp_pure
    twp_bind pl(&Occil.gaussianSelectorCoin #int (k : ℤ) #real x #())
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (twp_coin E (SbiiCredit F k x n z (factor k * ε)) k x hx) $$ Hcredit
    iintro %v ⟨%b, %hv, Hcredit⟩
    subst v
    cases b
    · isimp only [SbiiCredit, Bool.false_eq_true, ite_false] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      twp_pure
      rw [← Nat.cast_add_one]
      twp_bind pl(&(loop k x) #real z #int ((n + 1 : ℕ) : ℤ))
      iapply (tglWp_mono fun _ => tglWp_value)
      iapply IH $$ Hterm %z %hz' %(n + 1) Hcredit
    · twp_pures
      twp_value
      imodintro
      iexists n
      isimp only [SbiiCredit, ite_true] at Hcredit
      iframe Hcredit
      itrivial
  · twp_pures
    twp_value
    imodintro
    iexists n
    isimp only [SCreditAmp, of_decide_eq_true hyz, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- The Gaussian selector's exact exponential bias, including `x=0` and `x=1`. -/
theorem twp_gaussianSelector (E : CoPset) (F : Bool → ℝ≥0∞) (k : ℕ) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) :
    ⊢ ↯ (BCreditV F k x) -∗
      tglWp E pl(&Occil.gaussianSelector #int (k : ℤ) #real x)
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [gaussianSelectorCoin_openRec, gaussianSelectorCoin_closeRec]
  twp_bind pl(&(loop k x) #real x #0)
  iapply tglWp_wand
  isplitl [Hcredit]
  · isimp only [bCreditV_S0_eq F k x hx.1 hx.2] at Hcredit
    iapply (twp_loop E (BS0Credit F) k x hx x hx 0) $$ Hcredit
  iintro %v ⟨%n, %hv, Hcredit⟩
  subst v
  twp_pures
  rw [parity_beq]
  twp_value
  imodintro
  iexists decide (n % 2 = 0)
  isimp only [parity_credit] at Hcredit
  iframe Hcredit
  itrivial

end specification

end

end SampLib.GaussianSelector
