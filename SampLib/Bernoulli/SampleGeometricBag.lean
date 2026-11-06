import SampLib.Latent.UniformBagCoin

/-! # A conditional Bernoulli coin from a geometric digit of a shared uniform

The fresh selector chooses the cached head or a recursive tail coin equally.
Pointwise its bias is `(head+tail)/2`, the original latent uniform. The bag remains
owned, so later calls retain their conditional law given the same uniform.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.SampleGeometricBag

noncomputable section

private theorem prefix_step {p q r : List Bool} {b : Bool}
    (hs : UniformBag.stepRefines p b q) (hr : q <+: r) : p <+: b :: r := by
  rcases hs with ⟨rfl, _⟩ | rfl
  · exact List.nil_prefix
  · exact List.cons_prefix_cons.mpr ⟨rfl, hr⟩

section ownership

open Iris Iris.BI Iris.ProofMode

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF] [ECGS GF]
local bi (IProp GF)

private theorem restore (l tail : Loc) (p q : List Bool) (head : Bool)
    (hs : UniformBag.stepRefines p head q) (G : Bool → ℝ → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (v : Val rT) :
    iprop(appHeapFrag l (UniformBag.nodeVal head tail) ∗
      UniformBag.coinPost tail q (fun b u => G b (DyadicPosterior.half head u)) v) ⊢
      UniformBag.coinPost l p G v := by
  iintro ⟨Hl, Hpost⟩
  isimp only [UniformBag.coinPost] at Hpost
  ihave ⟨%b, %r, %hr, Htail, Hcredit⟩ := Hpost
  isimp only [UniformBag.coinPost]
  iexists b, head :: r
  isimp only [← DyadicPosterior.credit_cons head r (G b) (hG b)] at Hcredit
  ihave Hbag : UniformBag.owns l (head :: r) $$ [Hl Htail]
  · isimp only [UniformBag.owns]
    iexists tail
    iframe Hl Htail
  iframe Hbag Hcredit
  ipureintro
  exact ⟨hr.1, prefix_step hs hr.2⟩

end ownership

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def property (E : CoPset) : IProp GF := iprop(
  ∀ (l : Loc) (p : List Bool) (G : Bool → ℝ → ℝ≥0∞), ⌜∀ b, Measurable (G b)⌝ -∗
    UniformBag.owns l p -∗ ↯ (LatentBernoulli.credit p LatentBernoulli.bias G) -∗
      tglWp E pl(&Occil.sampleGeometricBag #loc l #()) (UniformBag.coinPost l p G))

private theorem twp_property (E : CoPset) (ε : ℝ≥0∞) (hε : 0 < ε) :
    iprop(↯ ε) ⊢ property (GF := GF) E := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩
  isimp only [property]
  iintro %l %p %G %hG Hbag Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  iterate 3 twp_pure
  isimp only [UniformBag.uniformBagStep_openRec, UniformBag.uniformBagStep_closeRec]
  twp_bind pl(&Occil.uniformBagStep #loc l)
  isimp only [LatentBernoulli.credit] at Hcredit
  iapply tglWp_wand
  isplitl [Hbag Hcredit]
  · iapply UniformBag.twp_uniformBagStep E l p (LatentBernoulli.kernel LatentBernoulli.bias G)
      (LatentBernoulli.measurable_kernel LatentBernoulli.measurable_bias hG)
    iframe Hbag Hcredit
  iintro %v ⟨%head, %tail, %q, %hv, Hl, Htail, Hcredit⟩
  rcases hv with ⟨rfl, hstep⟩
  twp_pure
  isimp only [FairCoin.fairCoin_openRec, FairCoin.fairCoin_closeRec]
  twp_bind pl(&Occil.fairCoin #())
  have hpreserve := LatentBernoulli.expectation q head G hG ε
  simp only [LatentBernoulli.credit] at hpreserve
  icombine Hcredit Hterm as Htotal
  isimp only [← hpreserve] at Htotal
  iapply ((FairCoin.fairCoin_distSpec E).wp (LatentBernoulli.selectorCredit q head G ε)
    (measurable_of_finite _) _) $$ Htotal
  iintro %select Hcredit
  cases select
  · isimp only [LatentBernoulli.selectorCredit, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    iterate 2 twp_pure
    twp_bind pl(&Occil.sampleGeometricBag #loc tail #())
    iapply tglWp_wand
    isplitl [Htail Hcredit Hterm IH]
    · ihave Hnext := IH $$ Hterm
      isimp only [property] at Hnext
      iapply Hnext $$ %tail %q %(fun b u => G b (DyadicPosterior.half head u))
        %(fun b => (hG b).comp (DyadicPosterior.measurable_half head)) Htail Hcredit
    iintro %v Hnext
    iapply (tglWp_value (v := v))
    iapply restore l tail p q head hstep G hG v
    iframe Hl Hnext
  · isimp only [LatentBernoulli.selectorCredit, ite_true] at Hcredit
    twp_pures
    twp_value
    imodintro
    isimp only [UniformBag.coinPost]
    iexists head, head :: q
    ihave Hbag : UniformBag.owns l (head :: q) $$ [Hl Htail]
    · isimp only [UniformBag.owns]
      iexists tail
      iframe Hl Htail
    iframe Hbag Hcredit
    ipureintro
    exact ⟨rfl, prefix_step hstep (List.prefix_refl _)⟩

/-- The sampled bit is Bernoulli(U), conditionally on the same owned lazy uniform. -/
theorem twp_sampleGeometricBag (E : CoPset) (l : Loc) (p : List Bool)
    (G : Bool → ℝ → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(UniformBag.owns l p ∗ ↯ (LatentBernoulli.credit p LatentBernoulli.bias G)) ⊢
      tglWp E pl(&Occil.sampleGeometricBag #loc l #()) (UniformBag.coinPost l p G) := by
  iintro ⟨Hbag, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  ihave Hnext := twp_property E ε hε $$ Hterm
  isimp only [property] at Hnext
  iapply Hnext $$ %l %p %G %hG Hbag Hcredit

/-- Reusable conditional specification; repeated calls retain their shared latent probability. -/
theorem sampleGeometricBag_coinSpec (E : CoPset) (l : Loc) :
    UniformBag.IsCoinSpec (GF := GF) E l pl(&Occil.sampleGeometricBag #loc l #())
      LatentBernoulli.bias where
  measurable_bias := LatentBernoulli.measurable_bias
  spec := twp_sampleGeometricBag E l

end specification

end

end SampLib.SampleGeometricBag
