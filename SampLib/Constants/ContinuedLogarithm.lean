import SampLib.Constants.Support.CriticalCoinRecursion
import SampLib.Uniform.RationalCoin
import SampLib.Uniform.FairCoin
import Samplers.Constants.Engines

/-! # Continued-logarithm coins

The coefficient at position `i` contributes `2^(-c_i)/(1+tail)`. Finite flags stop
immediately. Otherwise the fair two-call recursion is dominated by critical binary
branching; finite-tree continuation budgets provide total correctness.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ContinuedLogarithm

noncomputable section

structure Coefficient where
  exponent : ℕ
  last : Bool

def Coefficient.critical (c : Coefficient) : CriticalCoin.Coefficient where
  bias := RationalCoin.bias 1 (2 ^ c.exponent) (by norm_num)
    (by positivity) (by exact one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2))
  positive := by
    dsimp [RationalCoin.bias]
    push_cast
    positivity
  last := c.last

def coefficients (a : ℕ → Coefficient) (i : ℕ) := (a i).critical

abbrev bias (a : ℕ → Coefficient) (start : ℕ) := CriticalCoin.bias (coefficients a) start

/-- The oracle returns the nonnegative exponent and its final flag. -/
def encodeCoefficient {rT : Type} (c : Coefficient) : Val rT :=
  Val.pair (Val.int c.exponent) (Val.bool c.last)

@[pl_fold] private def power {rT : Type} : Exp rT := pl%
  rec twice n value := if n = #0 then value else twice (n - #1) (value * #2)

private theorem power_step (v : ℤ) (n : ℕ) :
    (v * 2) * 2 ^ n = v * 2 ^ (n + 1) := by ring

private theorem source_lc {rT : Type} :
    (Occil.Constants.continuedLogarithm : Exp rT).IsLocallyClosed := by is_lc

private theorem source_fv {rT : Type} :
    (Occil.Constants.continuedLogarithm : Exp rT).fv = ∅ := by
  simp [Occil.Constants.continuedLogarithm, Exp.fv,
    FairCoin.fairCoin_fv, RationalCoin.rationalCoin_fv]

private theorem source_open {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.continuedLogarithm =
      Occil.Constants.continuedLogarithm := (Exp.open_lc k e _ source_lc).symm

private theorem source_close {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.continuedLogarithm : Exp rT) =
      Occil.Constants.continuedLogarithm :=
  Exp.closeRec_fresh x _ k (by simp [source_fv])

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] source_open source_close
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec
  FairCoin.fairCoin_openRec FairCoin.fairCoin_closeRec

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_power (E : CoPset) (n : ℕ) (v : ℤ) :
    ⊢ tglWp E pl(&(power : Exp rT) #int (n : ℤ) #int v)
      (fun w : Val rT => iprop(⌜w = Val.int (v * 2 ^ n)⌝)) := by
  induction n generalizing v with
  | zero =>
    twp_pures
    twp_value
    imodintro
    ipureintro
    simp
  | succ n IH =>
    have hrec := IH (v * 2)
    simp [power, Exp.close, Exp.closeRec] at hrec
    iterate 7 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right, ← power_step]
    isimp only [Exp.ofVal]
    iapply hrec

private theorem direct_spec (E : CoPset) (c : Coefficient) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #1 #int (2 ^ c.exponent : ℤ))
      (RealCoin.law c.critical.bias) Val.bool :=
  RationalCoin.rationalCoin_distSpec E 1 (2 ^ c.exponent) (by norm_num)
    (by positivity) (by exact one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 2))

/-- One round of the source after it reads the coefficient `(exponent,last)` and computes
`2 ^ exponent`. -/
private def round (coefficient : Val rT) (i exponent : ℕ) (last : Bool) : Exp rT :=
  if last then pl(&Occil.rationalCoin #1 #int (2 ^ exponent : ℤ))
  else pl(if &Occil.fairCoin #() then &Occil.rationalCoin #1 #int (2 ^ exponent : ℤ)
    else if &Occil.Constants.continuedLogarithm &coefficient.fst (#int (i : ℤ) + #1)
      then #false
      else &Occil.Constants.continuedLogarithm &coefficient.fst #int (i : ℤ))

set_option maxHeartbeats 1000000 in
omit [ProbLangDist.IsUniformInt rT] in
/-- Reading a coefficient and computing its power of two leaves one round of the source. -/
private theorem twp_entry (E : CoPset) (coefficient : Val rT) (i exponent : ℕ) (last : Bool)
    (hentry : ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ)) (fun v : Val rT =>
      iprop(⌜v = Val.pair (Val.int exponent) (Val.bool last)⌝)))
    (Φ : Val rT → IProp GF) :
    tglWp E (round coefficient i exponent last) Φ ⊢
      tglWp E pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int (i : ℤ)) Φ := by
  iintro Hround
  iterate 3 twp_pure
  twp_bind pl(&coefficient.fst #int (i : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hentry
  iintro %v %hv
  subst v
  iterate 6 twp_pure
  twp_bind pl(&(power : Exp rT) #int (exponent : ℤ) #1)
  iapply tglWp_wand
  isplitl []
  · iapply twp_power E exponent 1
  iintro %v %hv
  subst v
  twp_pures
  isimp only [one_mul]
  cases last
  · twp_pure
    ieval (change _ ⊢ tglWp E (round coefficient i exponent false) Φ)
    iexact Hround
  · twp_pure
    ieval (change _ ⊢ tglWp E (round coefficient i exponent true) Φ)
    iexact Hround

private theorem twp_layer (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (horacle : ∀ i, CriticalCoin.Reachable (coefficients a) start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝)))
    (n : ℕ)
    (IH : ∀ i, CriticalCoin.Reachable (coefficients a) start i → ∀ (F : Bool → ℝ≥0∞),
      ⊢ ↯ (CriticalCoin.credit (coefficients a) n i F) -∗
        tglWp E pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int (i : ℤ))
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (i : ℕ) (hi : CriticalCoin.Reachable (coefficients a) start i) (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (CriticalCoin.credit (coefficients a) (n + 1) i F) -∗
      tglWp E pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_entry E coefficient i (a i).exponent (a i).last (horacle i hi)
  cases hlast : (a i).last
  · have hl : (coefficients a i).last = false := hlast
    simp only [round, Bool.false_eq_true, ite_false]
    twp_bind pl(&Occil.fairCoin #())
    isimp only [← CriticalCoin.expectation (coefficients a) n i hl F,
      ← RealCoin.lintegral_law] at Hcredit
    iapply ((FairCoin.fairCoin_distSpec E).wp
      (CriticalCoin.branchCredit (coefficients a) n i F) (measurable_of_countable _) _) $$ Hcredit
    iintro %selected Hcredit
    cases selected
    · iterate 2 twp_pure
      isimp only [CriticalCoin.branchCredit, Bool.false_eq_true, ite_false] at Hcredit
      twp_bind pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int ((i : ℤ) + 1))
      rw [← Nat.cast_add_one]
      iapply tglWp_wand
      isplitl [Hcredit]
      · iapply IH (i + 1) (CriticalCoin.reachable_next hi hl)
          (CriticalCoin.tailCredit (coefficients a) n i F) $$ Hcredit
      iintro %v ⟨%b, %hv, Hcredit⟩
      subst v
      cases b
      · twp_pure
        isimp only [CriticalCoin.tailCredit, Bool.false_eq_true, ite_false] at Hcredit
        ieval (
          change _ ⊢ tglWp E
            pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int (i : ℤ)) _)
        iapply IH i hi F $$ Hcredit
      · twp_pures
        twp_value
        imodintro
        iexists false
        isimp only [CriticalCoin.tailCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial
    · twp_pure
      isimp only [CriticalCoin.branchCredit, ite_true, coefficients,
        ← RealCoin.lintegral_law] at Hcredit
      iapply (direct_spec E (a i)).spec F (measurable_of_countable _) $$ Hcredit
  · have hl : (coefficients a i).last = true := hlast
    simp only [round, ite_true]
    isimp only [CriticalCoin.credit_last (coefficients a) n i hl F,
      coefficients, ← RealCoin.lintegral_law] at Hcredit
    iapply (direct_spec E (a i)).spec F (measurable_of_countable _) $$ Hcredit

/-- Finite or infinite continued logarithms, with no boundedness assumption on exponents. -/
theorem continuedLogarithm_distSpec (E : CoPset) (a : ℕ → Coefficient) (start : ℕ)
    (coefficient : Val rT)
    (horacle : ∀ i, CriticalCoin.Reachable (coefficients a) start i →
      ⊢ tglWp E pl(&coefficient.fst #int (i : ℤ))
        (fun v : Val rT => iprop(⌜v = encodeCoefficient (a i)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int (start : ℤ))
      (RealCoin.law (bias a start)) Val.bool := by
  exact CriticalCoin.distSpec_of_finite E
    (fun i => pl(&Occil.Constants.continuedLogarithm &coefficient.fst #int (i : ℤ)))
    (coefficients a) {i | CriticalCoin.Reachable (coefficients a) start i}
    (twp_layer E a start coefficient horacle) start
    (CriticalCoin.reachable_self (coefficients a) start) rfl

end specification

end

end SampLib.ContinuedLogarithm
