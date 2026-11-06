import SampLib.Bernoulli.Support.AlternatingPermutationPath
import SampLib.Bernoulli.Laws.AlternatingPermutationMixture
import SampLib.Discrete.Geometric
import SampLib.Bernoulli.Complement
import SampLib.Core.Syntax.ClosedExp
import Samplers.Bernoulli.Trigonometric

/-! # Alternating-permutation Bernoulli factories

A geometric count selects a parity and a finite alternating-uniform event. Its
Volterra generating function gives the secant and tangent success probabilities.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.AlternatingPermutation

noncomputable section

open AlternatingPermutationKernel AlternatingPermutationMixture

private def complementCoin (coin : Val ℝ) : Val ℝ :=
  ⟨.lam pl(~(&coin.fst #())), .lam (by is_lc), by is_lc⟩

private instance geometric_closed : ClosedExp (Occil.geometric : Exp ℝ) where
  lc := by is_lc
  fv := by simp [Occil.geometric, Exp.fv]

private instance alternating_closed :
    ClosedExp (Occil.FactoryExtra.alternatingPermutation : Exp ℝ) where
  lc := by is_lc
  fv := by
    simp [Occil.FactoryExtra.alternatingPermutation, Exp.fv, ClosedExp.closeRec, ClosedExp.fv]

private theorem parity_test (n : ℕ) (odd : Bool) :
    ((BaseLit.int ((n : ℤ) % 2) : BaseLit ℝ) == .int odd.toNat) =
      decide (n % 2 = odd.toNat) := by
  change ((n : ℤ) % 2 == (odd.toNat : ℤ)) = _
  by_cases h : n % 2 = odd.toNat
  · have ht : ((n : ℤ) % 2 == (odd.toNat : ℤ)) = true := beq_iff_eq.mpr (by omega)
    simp [h, ht]
  · have hf : ((n : ℤ) % 2 == (odd.toNat : ℤ)) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [h, hf]

private theorem complement_pos (p : unitInterval) (hp : (p : ℝ) < 1) :
    (0 : ℝ) < unitInterval.symm p := by
  simpa only [unitInterval.coe_symm_eq] using sub_pos.mpr hp

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

omit [ProbLangDist.IsUniformReal ℝ] in
private theorem complement_spec (E : CoPset) (p : unitInterval) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&(complementCoin coin).fst #())
      (RealCoin.law (unitInterval.symm p)) Val.bool where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&coin.fst #())
    isimp only [← Complement.expectation_preservation p F] at Hcredit
    iapply (hcoin.wp (fun b => F (!b)) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    twp_pures
    twp_value
    imodintro
    iexists !b
    iframe Hcredit
    ipureintro
    cases b <;> rfl

/-- Both parity branches of the original geometric/permutation construction. -/
theorem alternatingPermutation_distSpec (E : CoPset) (p : unitInterval)
    (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (odd : Bool) :
    IsDistSpec (GF := GF) E
      pl(&Occil.FactoryExtra.alternatingPermutation &coin.fst #int (odd.toNat : ℤ) #())
      (RealCoin.law (bias p odd)) Val.bool where
  spec F _ := by
    have hg := Geometric.geometric_distSpec E (unitInterval.symm p) (complement_pos p hp)
      (complementCoin coin) (complement_spec E p coin hcoin)
    simp only [complementCoin] at hg
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_bind pl(&Occil.geometric {Exp.lam pl(~(&coin.fst #()))} #())
    isimp only [RealCoin.lintegral_law, ← AlternatingPermutationMixture.expectation p odd F]
      at Hcredit
    iapply (hg.wp (fun n => RealCoin.credit (selectBias odd n) F)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %n Hcredit
    iterate 3 twp_pure
    rw [parity_test n odd]
    by_cases hpar : n % 2 = odd.toNat
    · rw [decide_eq_true hpar]
      twp_pure
      isimp only [selectBias, hpar, ite_true] at Hcredit
      cases n with
      | zero =>
        isimp only [eventBias_zero, RealCoin.credit_one] at Hcredit
        twp_bind pl(urand)
        iapply (twp_urand_exp (ε₂ := fun _ => F true) measurable_const (by simp)) $$ Hcredit
        iintro %x ⟨_, Hcredit⟩
        twp_pures
        twp_value
        imodintro
        iexists true
        iframe Hcredit
        itrivial
      | succ n =>
        twp_bind pl(urand)
        isimp only [← initial_expectation n F] at Hcredit
        iapply (twp_urand_exp (ε₂ := fun x => RealCoin.credit (pathBias n true x) F)
          (BernoulliMixture.measurable_credit _ (measurable_pathBias n true) F) le_rfl)
          $$ Hcredit
        iintro %x ⟨%hx, Hcredit⟩
        have hx' := mem_unifUnitSupport_real.mp hx
        iterate 2 twp_pure
        have hpath := AlternatingPermutationPath.twp_loop (GF := GF)
          E n 1 x ⟨hx'.1.le, hx'.2.le⟩ F
        rw [Nat.add_comm 1 n, AlternatingPermutationPath.up_one,
          AlternatingPermutationPath.loop_eq_code] at hpath
        simp only [Nat.cast_add, Nat.cast_one] at hpath
        isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_one]
        ieval (change _ ⊢ tglWp E (Exp.app
          (Exp.app (AlternatingPermutationPath.loopSource ((n : ℤ) + 1)) (.lit (.int 1)))
          (.lit (.real x))) _)
        rw [AlternatingPermutationPath.loopSource_eq_code]
        iapply hpath $$ Hcredit
    · rw [decide_eq_false hpar]
      twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [selectBias, hpar, ite_false, RealCoin.credit_zero] at Hcredit
      iframe Hcredit
      itrivial

/-- The even-count wrapper has probability `(1-p)/cos(p)`. -/
theorem complementOverCosine_distSpec (E : CoPset) (p : unitInterval)
    (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementOverCosine &coin.fst #())
      (RealCoin.law (bias p false)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    have hs := (alternatingPermutation_distSpec E p hp coin hcoin false).spec F hF
    simp only [Bool.toNat_false, Nat.cast_zero] at hs
    iapply hs $$ Hcredit

/-- The odd-count wrapper has probability `(1-p) tan(p)`. -/
theorem complementTimesTangent_distSpec (E : CoPset) (p : unitInterval)
    (hp : (p : ℝ) < 1) (coin : Val ℝ)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.FactoryExtra.complementTimesTangent &coin.fst #())
      (RealCoin.law (bias p true)) Val.bool where
  spec F hF := by
    iintro Hcredit
    iterate 2 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    have hs := (alternatingPermutation_distSpec E p hp coin hcoin true).spec F hF
    simp only [Bool.toNat_true, Nat.cast_one] at hs
    iapply hs $$ Hcredit

end specification

end

end SampLib.AlternatingPermutation
