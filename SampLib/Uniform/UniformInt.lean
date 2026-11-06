import SampLib.Templates
import SampLib.Uniform.Laws.UniformInt
import Samplers.Uniform
import Metrology.Iris.LocalBI

/-! # Uniform integer sampling -/

open Set ProbLang Finset
open scoped ENNReal

namespace SampLib.UniformInt

noncomputable section

/-- Closedness rewrites preserve the named sampler under enclosing binders. -/
theorem uniformInt_lc {rT : Type _} : (Occil.uniformInt : Exp rT).IsLocallyClosed := by is_lc

theorem uniformInt_fv {rT : Type _} : (Occil.uniformInt : Exp rT).fv = ∅ := by
  simp [Occil.uniformInt, Exp.fv]

@[simp] theorem uniformInt_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.uniformInt = Occil.uniformInt :=
  (Exp.open_lc k e _ uniformInt_lc).symm

@[simp] theorem uniformInt_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.uniformInt : Exp rT) = Occil.uniformInt :=
  Exp.closeRec_fresh x _ k (by simp [uniformInt_fv])

private theorem positive_test (n : ℕ) (hn : 0 < n) :
    decide ((0 : ℤ) < n) = true := decide_eq_true (by exact_mod_cast hn)

private theorem index_bounds {k : ℤ} {n : ℕ} (hk : 0 ≤ k ∧ k < (n : ℤ)) :
    k = (k.toNat : ℤ) ∧ k.toNat < n := by
  exact ⟨(Int.toNat_of_nonneg hk.1).symm, by omega⟩

section specification

open Iris Iris.BI Iris.ProofMode
open TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- CTE specification for a positive exclusive bound. -/
theorem twp_uniformInt (E : CoPset) (n : ℕ) (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ ((∑ k ∈ range n, F k) / n) -∗
      tglWp E pl(&Occil.uniformInt #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ⌜k < n⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  twp_pures
  rw [positive_test n hn]
  twp_pures
  iapply (twp_rand_exp (ε₂ := F) (by exact_mod_cast hn) ?_) $$ Hcredit
  · simp
  iintro %k ⟨%hk, Hcredit⟩
  iexists k.toNat
  iframe Hcredit
  isplit
  · ipureintro
    exact congrArg (fun z : ℤ => (Val.int z : Val rT)) (index_bounds hk).1
  · ipureintro
    exact (index_bounds hk).2

/-- Typed uniform distribution specification. -/
theorem uniformInt_distSpec (E : CoPset) (n : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E pl(&Occil.uniformInt #int (n : ℤ)) (law n)
      (fun k => Val.int (k : ℤ)) where
  spec F _ := by
    iintro Hcredit
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply twp_uniformInt E n (NeZero.pos n) F
      rw [lintegral_law]
      iexact Hcredit
    iintro %v ⟨%k, %hv, _, Hcredit⟩
    iexists k
    iframe Hcredit
    itrivial

end specification

end

end SampLib.UniformInt
