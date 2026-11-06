import SampLib.Syntax.ExponentialCount
import SampLib.Samplers.Complement

/-! # The exponential constructor's whole-part counter

Each decay success advances the counter. A failure stops, so the increment has
geometric law with parameter `1-q`, including immediate stopping at `q=0`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ExponentialCount

noncomputable section

abbrev stoppingBias (q : unitInterval) : unitInterval := unitInterval.symm q
abbrev law (q : unitInterval) := Geometric.law (stoppingBias q)

private theorem stopping_pos (q : unitInterval) (hq : (q : ℝ) < 1) :
    0 < (stoppingBias q : ℝ) := by
  change 0 < 1 - (q : ℝ)
  exact sub_pos.mpr hq

private theorem amplification_gt_one (q : unitInterval) (hq : (q : ℝ) < 1) :
    1 < Geometric.terminationFactor (stoppingBias q) := by
  change 1 < 1 + unitInterval.toNNReal (stoppingBias q)
  exact lt_add_of_pos_right _ (by exact_mod_cast stopping_pos q hq)

/-- Complementing the continuation turns decay survival into the geometric stopping recurrence. -/
theorem expectation (q : unitInterval) (hq : (q : ℝ) < 1)
    (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ b, Geometric.coinCredit (stoppingBias q) F ε (!b) ∂RealCoin.law q) =
      Geometric.credit (stoppingBias q) F + ε := by
  rw [Complement.expectation_preservation]
  exact Geometric.lintegral_coinCredit (stoppingBias q) (stopping_pos q hq) F ε

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Starting from an arbitrary integer adds a geometric number of decay successes. -/
theorem twp_count (E : CoPset) (q : unitInterval) (hq : (q : ℝ) < 1)
    (decay : Val rT)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #1) (RealCoin.law q) Val.bool)
    (whole : ℤ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (Geometric.credit (stoppingBias q) F) -∗
      tglWp E pl(&(Program.countVal decay).fst #int whole)
        (fun result : Val rT => iprop(∃ n : ℕ,
          ⌜result = Val.int (whole + n)⌝ ∗ ↯ (F n))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert! %whole %F
  iapply ErrorCredit.Induction.simple hε (amplification_gt_one q hq) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %whole %F Hcredit
  unfold Program.countVal Program.countCode
  twp_pures
  twp_bind pl(&decay.fst #1)
  icombine Hcredit Hterm as Hcredit
  isimp only [← expectation q hq F ε] at Hcredit
  iapply hdecay.wp (fun b => Geometric.coinCredit (stoppingBias q) F ε (!b))
    (measurable_of_countable _) _ $$ Hcredit
  iintro %b Hcredit
  cases b
  · isimp only [Bool.not_false, Geometric.coinCredit] at Hcredit
    ihave ⟨Hcredit, _⟩ := ErrorCredit.split $$ Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    iframe Hcredit
    ipureintro
    simp
  · isimp only [Bool.not_true, Geometric.coinCredit] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    twp_pure
    twp_pure
    iapply tglWp_wand
    isplitl [IH Hcredit Hterm]
    · iapply IH $$ Hterm %(whole + 1) %(fun n => F (n + 1)) Hcredit
    iintro %result ⟨%n, %hn, Hcredit⟩
    iexists n + 1
    iframe Hcredit
    ipureintro
    rw [hn, add_assoc, add_comm (1 : ℤ), ← Nat.cast_add_one]

/-- The literal loop started at zero supplies the constructor's geometric whole part. -/
theorem count_distSpec (E : CoPset) (q : unitInterval) (hq : (q : ℝ) < 1)
    (decay : Val rT)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #1) (RealCoin.law q) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(Program.countVal decay).fst #0)
      (law q) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    simpa only [Geometric.credit, zero_add] using
      wand_entails (twp_count E q hq decay hdecay 0 F)

end specification

end

end SampLib.ExponentialCount
