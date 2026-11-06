import SampLib.Distributions.EntropyPool
import SampLib.OwnedDistSpec
import Samplers.Weighted.Uniform

/-! # Heap operations for exact entropy recycling

A concrete pool has deterministic contents. The accepted rectangle returns its
remainder and stores its quotient; randomness enters only when the pool is
extended with fresh bits.
-/

open ProbLang

namespace SampLib.EntropyPool

/-- The physical pool stores its current integer and its number of possibilities. -/
abbrev poolVal {rT : Type} (value width : ℕ) : Val rT :=
  .pair (.int value) (.int width)

private theorem positive_test (bound : ℕ) (h : 0 < bound) :
    decide ((bound : ℤ) ≤ 0) = false := decide_eq_false (by exact_mod_cast not_le.mpr h)

private theorem width_test (bound width : ℕ) (h : bound ≤ width) :
    decide ((width : ℤ) < bound) = false := decide_eq_false (by exact_mod_cast not_lt.mpr h)

private theorem accept_test (bound width value : ℕ) (h : value < width / bound * bound) :
    decide ((value : ℤ) < (width : ℤ) / bound * bound) = true :=
  decide_eq_true (by exact_mod_cast h)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A completed rectangle consumes no randomness and keeps precisely the unused quotient. -/
theorem twp_recycledUniform_accept (E : CoPset) (pool : Loc)
    (bound width value : ℕ) (hb : 0 < bound) (hw : bound ≤ width)
    (hv : value < width / bound * bound) :
    appHeapFrag pool (poolVal (rT := rT) value width) ⊢
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (bound : ℤ))
        (fun v => iprop(⌜v = Val.int ((value % bound : ℕ) : ℤ)⌝ ∗
          appHeapFrag pool (poolVal (rT := rT) (value / bound) (width / bound)))) := by
  iintro Hpool
  twp_pures
  rw [positive_test bound hb]
  twp_pure
  twp_bind pl(!#loc pool)
  iapply twp_load
  iframe Hpool
  iintro Hpool
  twp_pures
  rw [width_test bound width hw]
  twp_pures
  rw [accept_test bound width value hv]
  twp_pures
  rw [← Int.natCast_ediv value bound, ← Int.natCast_ediv width bound,
    ← Int.natCast_emod value bound]
  twp_bind (Exp.store pl(#loc pool) (Exp.ofVal (poolVal (value / bound) (width / bound))))
  iapply (twp_store (v := poolVal (rT := rT) (value / bound) (width / bound)))
  iframe Hpool
  iintro Hpool
  twp_pures
  twp_value
  imodintro
  iframe Hpool
  ipureintro
  apply Val.ext
  simp only [Int.natCast_emod]

end specification

end SampLib.EntropyPool
