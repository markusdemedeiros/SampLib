import SampLib.EntropyPoolEntry

/-! # Exact quotient/remainder entropy recycling

A physical pool storing a valid rank `value < width` has a fixed joint law on the
returned remainder and the new stored pool. An accepted rectangle keeps its quotient.
Otherwise the residual bounded-width rank consumes fresh bits; positive slack pays
the finite cutoff tail. From the freshly allocated pool `(0,1)`, every draw is
uniform and resets the pool, so repeated draws are independent.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.RecycledUniform

open EntropyPool

noncomputable section

private theorem cutoff_narrow (n width : ℕ) (hw : width < n) : cutoff n width = 0 := by
  simp [cutoff, Nat.div_eq_of_lt hw]

private theorem residual_width (n width : ℕ) : width - cutoff n width = width % n := by
  have h := cutoff_add_mod n width
  omega

private theorem accepted_wide (n width value : ℕ) (ha : value < cutoff n width) :
    n ≤ width := by
  by_contra hw
  rw [cutoff_narrow n width (Nat.lt_of_not_ge hw)] at ha
  exact Nat.not_lt_zero _ ha

private theorem accepted_expectation (n value width : ℕ) (hn : 0 < n) (hv : value < width)
    (ha : value < cutoff n width) (F : JointResult → ℝ≥0∞) :
    (∫⁻ z, F z ∂recycledLaw n value width hn hv) = F (value % n, value / n, width / n) := by
  change (∫⁻ z, F z ∂recycledKernel n value width) = _
  rw [recycledKernel_expectation, ite_eq_left ha]

private theorem rejected_expectation (n value width : ℕ) (hn : 0 < n) (hv : value < width)
    (ha : ¬value < cutoff n width) (F : JointResult → ℝ≥0∞) :
    (∫⁻ z, F z ∂recycledLaw n value width hn hv) =
      ∫⁻ r, F (r, 0, 1) ∂boundedKernel n (width % n) (value - cutoff n width) := by
  change (∫⁻ z, F z ∂recycledKernel n value width) = _
  rw [recycledKernel_expectation, ite_eq_right ha]

private theorem single_expectation (F : ℕ → ℝ≥0∞) : (∫⁻ r, F r ∂UniformInt.law 1) = F 0 := by
  simp [UniformInt.lintegral_law]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The returned remainder, ownership of the updated pool, and its joint credit. -/
def jointPost (pool : Loc) (F : JointResult → ℝ≥0∞) (v : Val rT) : IProp GF :=
  iprop(∃ z : JointResult, ⌜v = Val.int (z.1 : ℤ)⌝ ∗
    appHeapFrag pool (poolVal (rT := rT) z.2.1 z.2.2) ∗ ↯ (F z))

/-- Positive slack pays the cutoff tail of a bounded-width rank's eventual law. -/
theorem twp_bounded (E : CoPset) (pool : Loc) (stored : Val rT) (n width value : ℕ)
    (hn : 0 < n) (hw : width < n) (hv : value < width) (F : ℕ → ℝ≥0∞) :
    iprop(appHeapFrag pool stored ∗ ↯ (∫⁻ r, F r ∂boundedKernel n width value)) ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) (loopPost pool n F) := by
  iintro ⟨Hpool, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  obtain ⟨T, hT⟩ := BitRecycler.exists_horizon n hn ε hε
  have hfund : BitRecycler.credit .lower n F T width value ≤
      (∫⁻ r, F r ∂boundedKernel n width value) + ε :=
    (horizon_lintegral_bound n T width value F hn hw hv).trans (add_le_add le_rfl hT)
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken hfund $$ Hcredit
  iapply twp_loop_horizon E pool stored n T width value hn hw hv F
  iframe Hpool Hcredit

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem reset_joint (pool : Loc) (n : ℕ) (F : JointResult → ℝ≥0∞) (v : Val rT) :
    loopPost pool n (fun r => F (r, 0, 1)) v ⊢ jointPost pool F v := by
  unfold loopPost jointPost
  iintro ⟨%r, %hr, Hpool, Hcredit⟩
  iexists (r, 0, 1)
  iframe Hpool Hcredit
  ipureintro
  exact hr.1

/-- A rejected rank changes only the local loop state; it continues from its residual. -/
private theorem twp_rejected (E : CoPset) (pool : Loc) (n value width : ℕ) (hn : 0 < n)
    (hv : value < width) (ha : ¬value < cutoff n width) (F : JointResult → ℝ≥0∞) :
    iprop(appHeapFrag pool (poolVal (rT := rT) value width) ∗
      ↯ (∫⁻ z, F z ∂recycledLaw n value width hn hv)) ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) (jointPost pool F) := by
  have hres := rejected_valid n width value hv ha
  iintro ⟨Hpool, Hcredit⟩
  isimp only [rejected_expectation n value width hn hv ha] at Hcredit
  iapply tglWp_mono (reset_joint pool n F)
  by_cases hwide : n ≤ width
  · iapply twp_recycledUniform_reject E pool n value width hwide ha
    rw [residual_width]
    iapply twp_bounded E pool _ n (width % n) (value - cutoff n width) hn
      (Nat.mod_lt _ hn) hres (fun r => F (r, 0, 1))
    iframe Hpool Hcredit
  · have hnarrow := Nat.lt_of_not_ge hwide
    isimp only [cutoff_narrow n width hnarrow, Nat.sub_zero, Nat.mod_eq_of_lt hnarrow]
      at Hcredit
    iapply twp_bounded E pool _ n width value hn hnarrow hv (fun r => F (r, 0, 1))
    iframe Hpool Hcredit

/-- Every valid stored pool: the exact joint law of the remainder and the updated pool. -/
theorem twp_recycledUniform (E : CoPset) (pool : Loc) (n value width : ℕ) (hn : 0 < n)
    (hv : value < width) (F : JointResult → ℝ≥0∞) :
    iprop(appHeapFrag pool (poolVal (rT := rT) value width) ∗
      ↯ (∫⁻ z, F z ∂recycledLaw n value width hn hv)) ⊢
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (n : ℤ))
        (jointPost pool F) := by
  by_cases ha : value < cutoff n width
  · iintro ⟨Hpool, Hcredit⟩
    isimp only [accepted_expectation n value width hn hv ha] at Hcredit
    iapply tglWp_wand
    isplitl [Hpool]
    · iapply twp_recycledUniform_accept E pool n width value hn
        (accepted_wide n width value ha) ha $$ Hpool
    iintro %v ⟨%hresult, Hpool⟩
    unfold jointPost
    iexists (value % n, value / n, width / n)
    iframe Hpool Hcredit
    ipureintro
    exact hresult
  · exact twp_recycledUniform_entry E pool n value width hn _ _
      (twp_rejected E pool n value width hn hv ha F)

/-- The source's fresh pool `(0,1)`: a uniform remainder, after which the pool is reset. -/
theorem recycledUniform_ownedDistSpec (E : CoPset) (pool : Loc) (n : ℕ) [NeZero n] :
    IsOwnedDistSpec (GF := GF) E (appHeapFrag pool (poolVal (rT := rT) 0 1))
      pl(&Occil.Weighted.recycledUniform #loc pool #int (n : ℤ))
      (UniformInt.law n) (fun r : ℕ => Val.int (r : ℤ)) where
  spec F _ := by
    have hn := NeZero.pos n
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hn) with hlarge | rfl
    · refine twp_recycledUniform_entry E pool n 0 1 hn _ _ ?_
      iintro ⟨Hpool, Hcredit⟩
      have hreset : (∫⁻ r, F r ∂boundedKernel n 1 0) = ∫⁻ r, F r ∂UniformInt.law n :=
        reset_expectation n hn hlarge F
      isimp only [← hreset] at Hcredit
      iapply tglWp_mono (fun v => ?_)
      rotate_left
      · iapply twp_bounded E pool _ n 1 0 hn hlarge (by decide) F
        iframe Hpool Hcredit
      unfold loopPost
      iintro ⟨%r, %hr, Hpool, Hcredit⟩
      iexists r
      iframe Hpool Hcredit
      ipureintro
      exact hr.1
    · iintro ⟨Hpool, Hcredit⟩
      isimp only [single_expectation F] at Hcredit
      iapply tglWp_wand
      isplitl [Hpool]
      · iapply twp_recycledUniform_accept E pool 1 1 0 (by decide) le_rfl (by decide) $$ Hpool
      iintro %v ⟨%hresult, Hpool⟩
      iexists 0
      iframe Hpool Hcredit
      ipureintro
      simpa using hresult

end specification

end

end SampLib.RecycledUniform
