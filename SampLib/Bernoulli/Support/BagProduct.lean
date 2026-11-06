import SampLib.Latent.UniformBagCoin
import SampLib.Bernoulli.CoinProduct

/-! # Products of conditional coins on one shared uniform -/

open ProbLang
open scoped ENNReal

namespace SampLib.BagProduct

noncomputable section

def bias (φ ψ : ℝ → unitInterval) (u : ℝ) : unitInterval := φ u * ψ u

private theorem measurable_bias {φ ψ : ℝ → unitInterval}
    (hφ : Measurable φ) (hψ : Measurable ψ) : Measurable (bias φ ψ) := by
  unfold bias
  fun_prop

def inputCredit (ψ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞) (b : Bool) : ℝ → ℝ≥0∞ :=
  if b then LatentBernoulli.kernel ψ G else G false

private theorem measurable_inputCredit {ψ : ℝ → unitInterval} (hψ : Measurable ψ)
    {G : Bool → ℝ → ℝ≥0∞} (hG : ∀ b, Measurable (G b)) (b : Bool) :
    Measurable (inputCredit ψ G b) := by
  cases b
  · exact hG false
  · exact LatentBernoulli.measurable_kernel hψ hG

/-- The product identity holds before integrating over the shared latent uniform. -/
theorem expectation (p : List Bool) (φ ψ : ℝ → unitInterval) (G : Bool → ℝ → ℝ≥0∞) :
    LatentBernoulli.credit p (bias φ ψ) G =
      LatentBernoulli.credit p φ (inputCredit ψ G) := by
  apply congrArg (DyadicPosterior.credit p)
  funext u
  simpa only [LatentBernoulli.kernel, inputCredit, ite_apply, bias, CoinProduct.law,
    CoinProduct.firstCredit, RealCoin.lintegral_law] using
    (CoinProduct.expectation_preservation (φ u) (ψ u) (fun b => G b u)).symm

/-- Structural abstraction preserves arbitrary callback free variables. -/
def callback {rT : Type} (left right : Val rT) : Val rT :=
  ⟨.lam pl(if &left.fst #() then &right.fst #() else #false), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- An independent ordinary coin can be used inside an owned shared-uniform kernel. -/
theorem of_distSpec (E : CoPset) (l : Loc) (e : Exp rT) (p : unitInterval)
    (h : IsDistSpec (GF := GF) E e (RealCoin.law p) Val.bool) :
    UniformBag.IsCoinSpec (GF := GF) E l e (fun _ => p) where
  measurable_bias := measurable_const
  spec q G hG := by
    iintro ⟨Hbag, Hcredit⟩
    isimp only [LatentBernoulli.credit_fixed_bias q p G hG,
      ← RealCoin.lintegral_law] at Hcredit
    iapply (h.wp (fun b => DyadicPosterior.credit q (G b)) (measurable_of_finite _) _)
      $$ Hcredit
    iintro %b Hcredit
    iapply UniformBag.coinPost_return l q q b G (List.prefix_refl _)
    iframe Hbag Hcredit

/-- Inline conditional calls preserve their pointwise product kernel. -/
theorem twp_product (E : CoPset) (l : Loc) (φ ψ : ℝ → unitInterval)
    (left right : Exp rT)
    (hleft : UniformBag.IsCoinSpec (GF := GF) E l left φ)
    (hright : UniformBag.IsCoinSpec (GF := GF) E l right ψ)
    (p : List Bool) (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p (bias φ ψ) G)) ⊢
      tglWp E pl(if &left then &right else #false) (UniformBag.coinPost l p G) := by
  iintro ⟨Hbag, Hcredit⟩
  isimp only [expectation p φ ψ G] at Hcredit
  twp_bind left
  iapply (hleft.wp p (inputCredit ψ G) (measurable_inputCredit hright.measurable_bias hG) _)
    $$ Hbag Hcredit
  iintro %b %q %hpq Hbag Hcredit
  cases b
  · twp_pures
    twp_value
    imodintro
    isimp only [inputCredit, Bool.false_eq_true, ite_false] at Hcredit
    iapply UniformBag.coinPost_return l p q false G hpq
    iframe Hbag Hcredit
  · twp_pure
    iapply tglWp_wand
    isplitl [Hbag Hcredit]
    · have hnext := hright.spec q G hG
      simp only [LatentBernoulli.credit] at hnext
      iapply hnext
      isimp only [inputCredit, ite_true] at Hcredit
      iframe Hbag Hcredit
    iintro %v Hpost
    iapply UniformBag.coinPost_weaken l p q G v hpq $$ Hpost

/-- Compose two conditional callbacks without forgetting their shared latent parameter. -/
theorem callback_coinSpec (E : CoPset) (l : Loc) (φ ψ : ℝ → unitInterval)
    (left right : Val rT)
    (hleft : UniformBag.IsCoinSpec (GF := GF) E l pl(&left.fst #()) φ)
    (hright : UniformBag.IsCoinSpec (GF := GF) E l pl(&right.fst #()) ψ) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(&(callback left right).fst #()) (bias φ ψ) where
  measurable_bias := measurable_bias hleft.measurable_bias hright.measurable_bias
  spec p G hG := by
    iintro Hcredit
    twp_pure
    iapply twp_product E l φ ψ pl(&left.fst #()) pl(&right.fst #()) hleft hright p G hG
      $$ Hcredit

end specification

end

end SampLib.BagProduct
