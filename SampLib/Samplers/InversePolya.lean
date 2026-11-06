import SampLib.Distributions.InverseUrn
import SampLib.Distributions.Urn
import SampLib.IndexedAbsorbingChain
import Samplers.Discrete.Counts

/-! # Failures before a prescribed number of reinforced-urn successes

First-marked waiting laws give the target distribution. At each required success,
a divergent cumulative hazard discharges the remaining failure tail.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.InversePolya

noncomputable section

open MeasureTheory (lintegral_congr lintegral_dirac)

abbrev law := InverseUrn.law

/-- Continuation credit after the first color at failure depth `n`. -/
def kernel (exit : ℕ → ℝ≥0∞) (n : ℕ) (c : ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then exit n else c

/-- Credit remaining after the next marked draw, including previous failures. -/
def successCredit (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ k, F (n + k) ∂law r (a + c) (b + n * c) c
    (ha.trans_le (Nat.le_add_right a c))

private theorem coin_continuation (a b c n : ℕ) (ha : 0 < a) :
    RealCoin.pmf (Urn.bias a (b + n * c)) false = UrnWaiting.continuation a b c n := by
  have ht : 0 < a + (b + n * c) := by omega
  simp [Urn.bias, ht, RealCoin.pmf, RationalCoin.bias,
    UrnWaiting.continuation, UrnWaiting.hazard, Nat.cast_add, Nat.cast_mul, add_assoc]

/-- The marked branch receives the lower-success-count expectation. -/
theorem coin_expectation (a b c n : ℕ) (ha : 0 < a)
    (exit : ℕ → ℝ≥0∞) (credit : ℝ≥0∞) :
    ∫⁻ color, kernel exit n credit color ∂RealCoin.law (Urn.bias a (b + n * c)) =
      (1 - UrnWaiting.continuation a b c n) * exit n +
        UrnWaiting.continuation a b c n * credit := by
  have hstop : RealCoin.pmf (Urn.bias a (b + n * c)) true =
      1 - UrnWaiting.continuation a b c n := by
    rw [← coin_continuation a b c n ha]
    have h := RealCoin.pmf_sum (Urn.bias a (b + n * c))
    exact ENNReal.eq_sub_of_add_eq (by simp [RealCoin.pmf]) h
  simp [RealCoin.lintegral_law, RealCoin.credit, kernel,
    hstop, coin_continuation a b c n ha]

/-- The urn recurrence includes the accumulated failure count in its credit. -/
theorem expectation (r a b c : ℕ) (ha : 0 < a) (F : ℕ → ℝ≥0∞) (n : ℕ) :
    ∫⁻ k, F (n + k) ∂law (r + 1) a (b + n * c) c ha =
      (1 - UrnWaiting.continuation a b c n) *
        successCredit r a b c ha F n +
      UrnWaiting.continuation a b c n *
        ∫⁻ k, F (n + 1 + k) ∂law (r + 1) a (b + (n + 1) * c) c ha := by
  unfold successCredit
  rw [InverseUrn.expectation]
  have hq : UrnWaiting.continuation a (b + n * c) c 0 =
      UrnWaiting.continuation a b c n := by
    simp [UrnWaiting.continuation, UrnWaiting.hazard, Nat.cast_add, Nat.cast_mul, add_assoc]
  rw [hq, show b + (n + 1) * c = b + n * c + c by ring]
  congr 2
  apply lintegral_congr
  intro k
  congr 1
  omega

private theorem valid_test (a : ℕ) (ha : 0 < a) :
    Bool.or (Bool.or (Bool.or false (decide ((a : ℤ) ≤ 0))) false) false = false := by
  have h : decide ((a : ℤ) ≤ 0) = false := decide_eq_false (by omega)
  rw [h]
  rfl

private theorem reinforce_failure (b c n : ℕ) :
    b + n * c + c = b + (n + 1) * c := by ring

private theorem shift_failure (n k : ℕ) : n + 1 + k = n + (k + 1) := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def post (F : ℕ → ℝ≥0∞) (n : ℕ) (v : Val rT) : IProp GF :=
  iprop(∃ (k : ℕ), ⌜v = Val.int (k : ℤ)⌝ ∗ ↯ (F (n + k)))

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem post_shift (F : ℕ → ℝ≥0∞) (n : ℕ) :
    (post (fun k => F (n + k)) 0 : Val rT → IProp GF) = post F n := by
  funext v
  simp only [post, Nat.zero_add]

private theorem urn_coin_spec (E : CoPset) (a b c n : ℕ) (ha : 0 < a) :
    IsDistSpec (GF := GF) E
      pl(&Occil.rationalCoin #int (a : ℤ) #int ((a : ℤ) + (b + n * c : ℕ)))
      (RealCoin.law (Urn.bias a (b + n * c))) Val.bool := by
  have ht : 0 < a + (b + n * c) := by omega
  simpa only [Urn.bias, dite_eq_left ht, Nat.cast_add] using
    RationalCoin.rationalCoin_distSpec (GF := GF) E
      (a : ℤ) ((a : ℤ) + (b + n * c : ℕ)) (by omega) (by omega) (by omega)

/-- The count law includes zero requested successes and zero reinforcement. -/
theorem twp_inversePolya (E : CoPset) (r a b c : ℕ) (ha : 0 < a)
    (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law r a b c ha) -∗
      tglWp E pl(&Occil.DiscreteExtra.inversePolya #int (r : ℤ) #int (a : ℤ)
        #int (b : ℤ) #int (c : ℤ)) (post F 0) := by
  induction r generalizing a b F with
  | zero =>
    iintro Hcredit
    twp_pures
    rw [valid_test a ha]
    twp_pures
    twp_value
    imodintro
    isimp only [post]
    iexists 0
    isimp only [law, InverseUrn.law, lintegral_dirac] at Hcredit
    iframe Hcredit
    itrivial
  | succ r ih =>
    have hstep (n : ℕ) (credit : ℝ≥0∞)
        (next : ⊢ ↯ credit -∗ tglWp E
          pl(&Occil.DiscreteExtra.inversePolya #int ((r + 1 : ℕ) : ℤ) #int (a : ℤ)
            #int ((b + (n + 1) * c : ℕ) : ℤ) #int (c : ℤ)) (post F (n + 1))) :
        ⊢ ↯ ((1 - UrnWaiting.continuation a b c n) *
          (successCredit r a b c ha F n) +
          UrnWaiting.continuation a b c n * credit) -∗
          tglWp E pl(&Occil.DiscreteExtra.inversePolya #int ((r + 1 : ℕ) : ℤ)
            #int (a : ℤ) #int ((b + n * c : ℕ) : ℤ) #int (c : ℤ)) (post F n) := by
      iintro Hcredit
      twp_pures
      rw [valid_test a ha]
      iterate 4 twp_pure
      simp only [RationalCoin.rationalCoin_openRec, RationalCoin.rationalCoin_closeRec]
      twp_bind pl(&Occil.rationalCoin #int (a : ℤ) #int ((a : ℤ) + (b + n * c : ℕ)))
      isimp only [← coin_expectation a b c n ha
        (successCredit r a b c ha F) credit]
        at Hcredit
      iapply ((urn_coin_spec E a b c n ha).wp
        (kernel (successCredit r a b c ha F) n credit) (measurable_of_countable _) _) $$ Hcredit
      iintro %color Hcredit
      cases color
      · iterate 2 twp_pure
        rw [← Nat.cast_add, reinforce_failure]
        simp only [Exp.ofVal]
        twp_bind pl(&Occil.DiscreteExtra.inversePolya #int ((r + 1 : ℕ) : ℤ)
          #int (a : ℤ) #int ((b + (n + 1) * c : ℕ) : ℤ) #int (c : ℤ))
        iapply tglWp_wand
        isplitl [Hcredit]
        · isimp only [kernel, Bool.false_eq_true, ite_false] at Hcredit
          iapply next $$ Hcredit
        iintro %v Hcredit
        isimp only [post] at Hcredit
        ihave ⟨%k, %hv, Hcredit⟩ := Hcredit
        subst v
        twp_pures
        twp_value
        imodintro
        isimp only [post]
        iexists (k + 1)
        rw [shift_failure]
        iframe Hcredit
        ipureintro
        apply Val.ext
        simp [add_comm]
      · iterate 3 twp_pure
        rw [Nat.cast_add_one, add_sub_cancel_right, ← Nat.cast_add]
        isimp only [kernel, ite_true, successCredit] at Hcredit
        have h := ih (a + c) (b + n * c) (by omega) (fun k => F (n + k))
        rw [post_shift] at h
        simp only [Exp.ofVal]
        change _ ⊢ tglWp E
          pl(&Occil.DiscreteExtra.inversePolya #int (r : ℤ) #int ((a + c : ℕ) : ℤ)
            #int ((b + n * c : ℕ) : ℤ) #int (c : ℤ)) (post F n)
        iapply h
    have h := AbsorbingChain.twp_of_survival_indexed E
      (fun n => pl(&Occil.DiscreteExtra.inversePolya #int ((r + 1 : ℕ) : ℤ)
        #int (a : ℤ) #int ((b + n * c : ℕ) : ℤ) #int (c : ℤ))) (post F)
      (UrnWaiting.continuation a b c)
      (fun n => (1 - UrnWaiting.continuation a b c n) *
        successCredit r a b c ha F n)
      (fun n => ∫⁻ k, F (n + k) ∂law (r + 1) a (b + n * c) c ha)
      (expectation r a b c ha F) hstep 0 rfl (UrnWaiting.absorbs a b c ha)
    simpa only [Nat.zero_add, Nat.zero_mul, Nat.add_zero] using h

/-- Typed inverse-urn law on the complete nonnegative-input terminating domain. -/
theorem inversePolya_distSpec (E : CoPset) (r a b c : ℕ) (ha : 0 < a) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.inversePolya #int (r : ℤ) #int (a : ℤ)
        #int (b : ℤ) #int (c : ℤ)) (law r a b c ha) (fun k : ℕ => Val.int (k : ℤ)) where
  spec F _ := by
    have h := twp_inversePolya (GF := GF) E r a b c ha F
    unfold post at h
    simpa only [Nat.zero_add] using wand_entails h

end specification

end

end SampLib.InversePolya
