import SampLib.EntropyPoolLoop
import SampLib.Distributions.EntropyPoolKernel

/-! # Entry and deterministic rejection for an exact entropy pool

Loading the physical pool preserves its ownership. Rejection changes the local
rank only; the original heap value remains owned until the eventual store.
-/

open ProbLang

namespace SampLib.EntropyPool

noncomputable section

private theorem positive_test (n : ℕ) (hn : 0 < n) : decide ((n : ℤ) ≤ 0) = false :=
  decide_eq_false (by exact_mod_cast not_le.mpr hn)

private theorem wide_test (n width : ℕ) (hw : n ≤ width) :
    decide ((width : ℤ) < n) = false := decide_eq_false (by exact_mod_cast not_lt.mpr hw)

private theorem cutoff_cast (n width : ℕ) :
    (width : ℤ) / n * n = (cutoff n width : ℤ) := by
  simp only [cutoff, Nat.cast_mul, Int.natCast_ediv]

private theorem cutoff_le (n width : ℕ) : cutoff n width ≤ width := Nat.div_mul_le_self width n

private theorem rejected_test (n value width : ℕ) (ha : ¬value < cutoff n width) :
    decide ((value : ℤ) < (width : ℤ) / n * n) = false := by
  rw [cutoff_cast]
  exact decide_eq_false (by exact_mod_cast ha)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Read the real pool, then continue with exactly the source's local loop. -/
theorem twp_recycledUniform_entry (E : CoPset) (pool : Loc) (n value width : ℕ)
    (hn : 0 < n) (R : IProp GF) (Φ : Val rT → IProp GF)
    (hcontinue : iprop(appHeapFrag pool (poolVal (rT := rT) value width) ∗ R) ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) Φ) :
    iprop(appHeapFrag pool (poolVal (rT := rT) value width) ∗ R) ⊢
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (n : ℤ)) Φ := by
  iintro ⟨Hpool, HR⟩
  twp_pures
  rw [positive_test n hn]
  twp_pure
  twp_bind pl(!#loc pool)
  iapply twp_load
  iframe Hpool
  iintro Hpool
  iterate 4 twp_pure
  ieval (
    change _ ⊢ tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) Φ)
  iapply hcontinue
  iframe Hpool HR

omit [ProbLangDist.IsUniformInt rT] in
/-- A high-tail rejection is purely local and does not modify the physical pool. -/
theorem twp_recycledUniform_reject (E : CoPset) (pool : Loc) (n value width : ℕ)
    (hw : n ≤ width) (ha : ¬value < cutoff n width) (Φ : Val rT → IProp GF) :
    tglWp E pl(&(loop pool n) #int ((value - cutoff n width : ℕ) : ℤ)
      #int ((width - cutoff n width : ℕ) : ℤ)) Φ ⊢
      tglWp E pl(&(loop pool n) #int (value : ℤ) #int (width : ℤ)) Φ := by
  iintro H
  iapply Program.twp_open E pool n value width
  unfold Program.step
  twp_pures
  rw [wide_test n width hw]
  twp_pures
  rw [rejected_test n value width ha]
  iterate 3 twp_pure
  rw [cutoff_cast]
  rw [← Nat.cast_sub (Nat.le_of_not_gt ha), ← Nat.cast_sub (cutoff_le n width)]
  isimp only [loop_openRec, loop_closeRec, Exp.ofVal]
  iexact H

end specification

end

end SampLib.EntropyPool
