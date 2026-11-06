import SampLib.PSRN.Support.ExponentialCount

/-! Literal decay-counter clients retain a frame, offsets, and arbitrary infinite credits. -/

open ProbLang
open scoped ENNReal

namespace SampLib.ExponentialCount.ProducerCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem offset_framed (E : CoPset) (q : unitInterval) (hq : (q : ℝ) < 1)
    (decay : Val rT)
    (hdecay : IsDistSpec (GF := GF) E pl(&decay.fst #1) (RealCoin.law q) Val.bool)
    (whole : ℤ) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (Geometric.credit (stoppingBias q) F) ∗ R) ⊢
      tglWp E pl(&(Program.countVal decay).fst #int whole)
        (fun result : Val rT => iprop(∃ n : ℕ,
          ⌜result = Val.int (whole + n)⌝ ∗ ↯ (F n) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply twp_count E q hq decay hdecay whole F $$ Hcredit
  iintro %result ⟨%n, %hn, Hcredit⟩
  iexists n
  iframe Hcredit HR
  itrivial

private def falseDecay : Val rT := ⟨pl(fun divisor, #false), .lam (by is_lc), by is_lc⟩

private theorem falseDecay_spec (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(falseDecay : Val rT).fst #1)
      (RealCoin.law 0) Val.bool where
  spec F _ := by
    iintro Hcredit
    isimp only [RealCoin.lintegral_law] at Hcredit
    isimp [RealCoin.credit, RealCoin.pmf] at Hcredit
    unfold falseDecay
    twp_pures
    twp_value
    imodintro
    iexists false
    iframe Hcredit
    itrivial

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&(Program.countVal (falseDecay : Val rT)).fst #0)
      (law 0) (fun n : ℕ => Val.int (n : ℤ)) :=
  count_distSpec E 0 (by norm_num) falseDecay (falseDecay_spec E)

private theorem credit_zero_q (F : ℕ → ℝ≥0∞) :
    Geometric.credit (stoppingBias 0) F = F 0 := by
  simpa [Geometric.credit, Geometric.law, stoppingBias] using
    ProbabilityTheory.lintegral_geometricMeasure_succ (1 : unitInterval) (by norm_num) F

example : Geometric.credit (stoppingBias 0) (fun n => if n = 0 then 0 else ∞) = 0 := by
  rw [credit_zero_q]
  rfl

#print axioms offset_framed
#print axioms twp_count
#print axioms count_distSpec
#print axioms expectation

end

end SampLib.ExponentialCount.ProducerCallers
