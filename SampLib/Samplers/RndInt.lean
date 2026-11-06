import SampLib.Samplers.UniformInt
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # Uniform integers with an inclusive upper bound -/

open Set ProbLang Finset
open scoped ENNReal

namespace SampLib.RndInt

noncomputable section

/-- Uniform law on `0, …, hi`. -/
abbrev law (hi : ℕ) := UniformInt.law (hi + 1)

/-- An inclusive bound contributes `hi+1` equally weighted outcomes. -/
theorem expectation (hi : ℕ) (F : ℕ → ℝ≥0∞) :
    ∫⁻ k, F k ∂law hi = (∑ k ∈ range (hi + 1), F k) / ((hi + 1 : ℕ) : ℝ≥0∞) :=
  UniformInt.lintegral_law (hi + 1) F

private theorem credit_zero (F : ℕ → ℝ≥0∞) : ∫⁻ k, F k ∂law 0 = F 0 := by
  simp [expectation]

theorem rndInt_lc {rT : Type _} : (Occil.rndInt : Exp rT).IsLocallyClosed := by is_lc

theorem rndInt_fv {rT : Type _} : (Occil.rndInt : Exp rT).fv = ∅ := by
  simp [Occil.rndInt, UniformInt.uniformInt_fv, Exp.fv]

@[simp] theorem rndInt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.rndInt = Occil.rndInt :=
  (Exp.open_lc k e _ rndInt_lc).symm

@[simp] theorem rndInt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.rndInt : Exp rT) = Occil.rndInt :=
  Exp.closeRec_fresh x _ k (by simp [rndInt_fv])

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem twp_rndInt (E : CoPset) (hi : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law hi) -∗ tglWp E pl(&Occil.rndInt #int (hi : ℤ))
      (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  cases hi with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists 0
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n =>
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&Occil.uniformInt #int ((n + 1 + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (UniformInt.uniformInt_distSpec E (n + 1 + 1)).spec F
      (measurable_of_countable _) $$ Hcredit

/-- The zero endpoint is deterministic; every other valid upper bound is uniform. -/
theorem rndInt_distSpec (E : CoPset) (hi : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.rndInt #int (hi : ℤ)) (law hi)
      (fun k => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_rndInt E hi F)

end specification

end

end SampLib.RndInt
