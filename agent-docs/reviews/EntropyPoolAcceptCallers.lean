import SampLib.EntropyPool

open ProbLang SampLib

#print axioms EntropyPool.twp_recycledUniform_accept
#print axioms EntropyPool.split

section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

example (E : CoPset) (pool : Loc) (bound width value : ℕ) (hb : 0 < bound)
    (hw : bound ≤ width) (hv : value < width / bound * bound) (R : IProp GF) :
    ⊢ R -∗ appHeapFrag pool (EntropyPool.poolVal (rT := rT) value width) -∗
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (bound : ℤ))
        (fun v => iprop(⌜v = Val.int ((value % bound : ℕ) : ℤ)⌝ ∗ R ∗
          appHeapFrag pool (EntropyPool.poolVal (rT := rT) (value / bound) (width / bound)))) := by
  iintro HR Hpool
  iapply tglWp_wand
  isplitl [Hpool]
  · iapply (EntropyPool.twp_recycledUniform_accept E pool bound width value hb hw hv) $$ Hpool
  iintro %v ⟨%hv, Hpool⟩
  iframe HR Hpool
  itrivial

/-- A known complete two-cell pool returns its known remainder, rather than a fresh fair bit. -/
example (E : CoPset) (pool : Loc) :
    appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 2) ⊢
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (2 : ℤ))
        (fun v => iprop(⌜v = Val.int (0 : ℤ)⌝ ∗
          appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1))) := by
  simpa only [Nat.reduceDiv, Nat.reduceMod, Nat.cast_zero, Nat.cast_ofNat] using
    (EntropyPool.twp_recycledUniform_accept (rT := rT) (GF := GF) E pool 2 2 0
      (by decide) (by decide) (by decide))

end
