import SampLib.Uniform.Laws.ModulusReduction
import SampLib.Uniform.Laws.UniformSupport
import SampLib.Core.SupportedSpec
import SampLib.Core.Syntax.ClosedExp

/-! # Exact uniform integers from another source modulus

Small targets retain complete residue blocks. Large targets recursively add a
low digit before interval rejection. Each enclosing range accepts at least half.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.UniformFromModulus

noncomputable section

private theorem limit_repr (modulus n : ℕ) (hm : 2 ≤ modulus) :
    ((modulus : ℤ) - 1) / n * n = (ModulusReduction.limit modulus n : ℤ) := by
  have hsub : ((modulus - 1 : ℕ) : ℤ) = (modulus : ℤ) - 1 := by omega
  rw [← hsub]
  simp only [ModulusReduction.limit, Nat.cast_mul, Int.natCast_div]
  exact mul_comm _ _

private theorem width_repr (modulus n : ℕ) (hn : 0 < n) :
    ((n : ℤ) - 1) / modulus + 1 = (ModulusReduction.width modulus n : ℤ) := by
  have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  rw [← hsub]
  simp only [ModulusReduction.width, Nat.cast_add, Int.natCast_div, Nat.cast_one]

private theorem valid_test (modulus n : ℕ) (hm : 2 ≤ modulus) (hn : 0 < n) :
    (decide ((modulus : ℤ) < 2) || decide ((n : ℤ) ≤ 0)) = false := by
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

private instance source_closed {rT : Type _} : ClosedExp (Occil.uniformFromModulus : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.uniformFromModulus, Exp.fv]

private instance call_closed {rT : Type _} (modulus n : ℕ) :
    ClosedExp (pl(&Occil.uniformFromModulus #int (modulus : ℤ) #int (n : ℤ)) : Exp rT) where
  lc := by is_lc
  fv := by simp [Exp.fv, ClosedExp.fv]

private def smallRetry {rT : Type _} (modulus n : ℕ) : Exp rT := pl%
  rec go u :=
    let x := rand(#int (modulus : ℤ), #());
    if x < #int (n : ℤ) then x else
      if x < #int (ModulusReduction.limit modulus n : ℤ)
      then x % #int (n : ℤ) else go #()

private def largeRetry {rT : Type _} (modulus n : ℕ) (lowDraw : Exp rT) : Exp rT :=
  Exp.subst (pl% rec go u :=
    let high := rand(#int (modulus : ℤ), #());
    let low := supply;
    let x := #int (ModulusReduction.width modulus n : ℤ) * high + low;
    if x < #int (n : ℤ) then x else go #()) (.named "supply") lowDraw

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem native_distSpec (E : CoPset) (n : ℕ) [NeZero n] :
    IsDistSpec (GF := GF) E pl(rand(#int (n : ℤ), #())) (UniformInt.law n)
      (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  iintro Hcredit
  isimp only [UniformInt.lintegral_law] at Hcredit
  iapply (twp_rand_exp (ε₂ := F) (by exact_mod_cast NeZero.pos n) ?_) $$ Hcredit
  · simp
  iintro %k ⟨%hk, Hcredit⟩
  iexists k.toNat
  iframe Hcredit
  ipureintro
  exact congrArg (fun z : ℤ => (Val.int z : Val rT)) (Int.toNat_of_nonneg hk.1).symm

private theorem twp_equal (E : CoPset) (modulus : ℕ) [NeZero modulus]
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law modulus) -∗
      tglWp E pl(&(smallRetry modulus modulus) #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  iintro Hcredit
  iterate 2 twp_pure
  twp_bind pl(rand(#int (modulus : ℤ), #()))
  iapply ((native_distSpec E modulus).wp_supported (fun k => k < modulus)
    (Set.to_countable _).measurableSet (UniformInt.ae_lt modulus) F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %k %hk Hcredit
  twp_pures
  rw [show decide ((k : ℤ) < (modulus : ℤ)) = true by exact_mod_cast decide_eq_true hk]
  twp_pures
  twp_value
  imodintro
  iexists k
  iframe Hcredit
  itrivial

private theorem twp_small (E : CoPset) (modulus n : ℕ) (hn : 0 < n)
    (hnm : n < modulus) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) -∗
      tglWp E pl(&(smallRetry modulus n) #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  let : NeZero modulus := ⟨by omega⟩
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (by norm_num : 1 < (2 : ℝ≥0)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  twp_bind pl(rand(#int (modulus : ℤ), #()))
  icombine Hcredit Hterm as Htotal
  ihave Hkernel := ErrorCredit.weaken
    (ModulusReduction.small_expectation modulus n hn hnm F ε) $$ Htotal
  iapply ((native_distSpec E modulus).wp (ModulusReduction.smallKernel modulus n F ε)
    (measurable_of_countable _) _) $$ Hkernel
  iintro %k Hcredit
  twp_pures
  by_cases hk : k < n
  · rw [show decide ((k : ℤ) < (n : ℤ)) = true by exact_mod_cast decide_eq_true hk]
    twp_pures
    twp_value
    imodintro
    iexists k
    isimp only [ModulusReduction.smallKernel, ite_eq_left hk] at Hcredit
    iframe Hcredit
    itrivial
  · rw [show decide ((k : ℤ) < (n : ℤ)) = false by exact decide_eq_false (by omega)]
    twp_pures
    by_cases hlimit : k < ModulusReduction.limit modulus n
    · rw [show decide ((k : ℤ) < (ModulusReduction.limit modulus n : ℤ)) = true by
        exact_mod_cast decide_eq_true hlimit]
      twp_pures
      twp_value
      imodintro
      iexists k % n
      isimp only [ModulusReduction.smallKernel, ite_eq_right hk, ite_eq_left hlimit] at Hcredit
      iframe Hcredit
      ipureintro
      exact Val.ext (by simp only [Int.natCast_mod])
    · rw [show decide ((k : ℤ) < (ModulusReduction.limit modulus n : ℤ)) = false by
        exact decide_eq_false (by omega)]
      twp_pure
      isimp only [ModulusReduction.smallKernel, ite_eq_right hk, ite_eq_right hlimit] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      isimp [smallRetry, Exp.close, Exp.closeRec] at IH
      iapply IH $$ Hterm Hcredit

private theorem twp_large (E : CoPset) (modulus n : ℕ) (hm : 2 ≤ modulus)
    (hmn : modulus < n) (lowDraw : Exp rT) [ClosedExp lowDraw]
    (hlow : IsDistSpec (GF := GF) E lowDraw
      (UniformInt.law (ModulusReduction.width modulus n)) (fun k : ℕ => Val.int (k : ℤ)))
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) -∗
      tglWp E pl(&(largeRetry modulus n lowDraw) #())
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  let : NeZero modulus := ⟨by omega⟩
  have hlow_lc : lowDraw.IsLocallyClosed := ClosedExp.lc
  iintro Hcredit
  simp [largeRetry, Exp.subst, Exp.close, Exp.closeRec]
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (by norm_num : 1 < (2 : ℝ≥0)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  twp_bind pl(rand(#int (modulus : ℤ), #()))
  icombine Hcredit Hterm as Htotal
  ihave Hkernel := ErrorCredit.weaken
    (ModulusReduction.large_expectation modulus n hm hmn F ε) $$ Htotal
  iapply ((native_distSpec E modulus).wp (fun high =>
    ∫⁻ low, UniformRejection.kernel n F ε (ModulusReduction.width modulus n * high + low)
      ∂UniformInt.law (ModulusReduction.width modulus n)) (measurable_of_countable _) _)
    $$ Hkernel
  iintro %high Hcredit
  twp_pure
  simp only [ClosedExp.openRec]
  twp_bind lowDraw
  iapply (hlow.wp (fun low => UniformRejection.kernel n F ε
    (ModulusReduction.width modulus n * high + low)) (measurable_of_countable _) _) $$ Hcredit
  iintro %low Hcredit
  twp_pures
  rw [← Nat.cast_mul, ← Nat.cast_add]
  by_cases hk : ModulusReduction.width modulus n * high + low < n
  · rw [show decide (((ModulusReduction.width modulus n * high + low : ℕ) : ℤ) < n) =
        true by exact_mod_cast decide_eq_true hk]
    twp_pures
    twp_value
    imodintro
    iexists ModulusReduction.width modulus n * high + low
    isimp only [UniformRejection.kernel, ite_eq_left hk] at Hcredit
    iframe Hcredit
    itrivial
  · rw [show decide (((ModulusReduction.width modulus n * high + low : ℕ) : ℤ) < n) =
        false by exact decide_eq_false (by omega)]
    twp_pure
    isimp only [UniformRejection.kernel, ite_eq_right hk] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    simp only [ClosedExp.openRec]
    isimp only [ENNReal.coe_two] at IH
    iapply IH $$ Hterm Hcredit

private theorem twp_uniformFromModulus (E : CoPset) (modulus n : ℕ) (hm : 2 ≤ modulus)
    (hn : 0 < n) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂UniformInt.law n) -∗
      tglWp E pl(&Occil.uniformFromModulus #int (modulus : ℤ) #int (n : ℤ))
        (fun v : Val rT => iprop(∃ k : ℕ, ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n using Nat.strong_induction_on generalizing modulus F with
  | h n ih =>
    let : NeZero modulus := ⟨by omega⟩
    have hlow (hbig : modulus < n) : IsDistSpec (GF := GF) E
        pl(&Occil.uniformFromModulus #int (modulus : ℤ)
          #int (ModulusReduction.width modulus n : ℤ))
        (UniformInt.law (ModulusReduction.width modulus n)) (fun k : ℕ => Val.int (k : ℤ)) := by
      refine ⟨fun G _ => ?_⟩
      exact wand_entails (ih _ (ModulusReduction.width_lt modulus n hm hbig)
        modulus hm (ModulusReduction.width_pos modulus n) G)
    have hlarge (hbig : modulus < n) := twp_large (rT := rT) (GF := GF) E modulus n hm hbig
      pl(&Occil.uniformFromModulus #int (modulus : ℤ)
        #int (ModulusReduction.width modulus n : ℤ)) (hlow hbig) F
    simp [largeRetry, Exp.subst, Occil.uniformFromModulus, Exp.close, Exp.closeRec] at hlarge
    have hsmall (hlt : n < modulus) := twp_small (rT := rT) (GF := GF) E modulus n hn hlt F
    simp [smallRetry, Exp.close, Exp.closeRec] at hsmall
    have hequal := twp_equal (rT := rT) (GF := GF) E modulus F
    simp [smallRetry, Exp.close, Exp.closeRec] at hequal
    iintro Hcredit
    twp_pures
    rw [valid_test modulus n hm hn]
    twp_pures
    by_cases hnm : n ≤ modulus
    · rw [show decide ((n : ℤ) ≤ (modulus : ℤ)) = true by exact_mod_cast decide_eq_true hnm]
      iterate 4 twp_pure
      rw [limit_repr modulus n hm]
      iterate 2 twp_pure
      by_cases heq : n = modulus
      · subst n
        iapply hequal $$ Hcredit
      · iapply hsmall (lt_of_le_of_ne hnm heq) $$ Hcredit
    · rw [show decide ((n : ℤ) ≤ (modulus : ℤ)) = false by
        exact decide_eq_false (by omega)]
      iterate 4 twp_pure
      rw [width_repr modulus n hn]
      iterate 2 twp_pure
      iapply hlarge (Nat.lt_of_not_ge hnm) $$ Hcredit

/-- Every positive target can be sampled exactly from any source modulus at least two. -/
theorem uniformFromModulus_distSpec (E : CoPset) (modulus n : ℕ) (hm : 2 ≤ modulus)
    [NeZero n] :
    IsDistSpec (GF := GF) E
      pl(&Occil.uniformFromModulus #int (modulus : ℤ) #int (n : ℤ))
      (UniformInt.law n) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := wand_entails (twp_uniformFromModulus E modulus n hm (NeZero.pos n) F)

end specification

end

end SampLib.UniformFromModulus
