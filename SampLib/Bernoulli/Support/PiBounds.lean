import SampLib.Bernoulli.Laws.PiBoundsDefs
import SampLib.Bernoulli.Support.RealEnclosureEncoding
import SampLib.Templates
import SampLib.Core.SamplerStep
import SampLib.Core.ProofMode.BindFrom
import Samplers.Constants.Pi

/-! # Computing the rational Machin enclosures

The deterministic loops retain their integer numerators and denominators exactly.
Their analytic interpretation is supplied separately by the arctangent series.
-/

open ProbLang

namespace SampLib.PiBounds

export RealEnclosure (encodeTriple)

private def addTerm {rT : Type _} (q n : ℕ) : Exp rT := pl%
  rec addTerm k power numerator denominator :=
    let termDenominator := (#2 * k + #1) * power;
    if k = #int (n : ℤ) then
      let middle := numerator * termDenominator;
      let commonDenominator := denominator * termDenominator;
      if k % #2 = #0 then (middle, (middle + denominator, commonDenominator))
      else (middle - denominator, (middle, commonDenominator))
    else
      let sign := (if k % #2 = #0 then #1 else #(-1));
      addTerm (k + #1) (power * #int (q : ℤ) * #int (q : ℤ))
        (numerator * termDenominator + sign * denominator)
        (denominator * termDenominator)

private def addTermValue {rT : Type _} (q n : ℕ) : Val rT :=
  ⟨addTerm q n, .fix (by is_lc), by is_lc⟩

private theorem addTermValue_fst {rT : Type _} (q n : ℕ) :
    (addTermValue (rT := rT) q n).fst = addTerm q n := rfl

theorem arctanReciprocalBounds_lc {rT : Type _} :
    (Occil.Constants.arctanReciprocalBounds : Exp rT).IsLocallyClosed := by is_lc

theorem arctanReciprocalBounds_fv {rT : Type _} :
    (Occil.Constants.arctanReciprocalBounds : Exp rT).fv = ∅ := by
  simp [Occil.Constants.arctanReciprocalBounds, Exp.fv]

@[simp] theorem arctanReciprocalBounds_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.arctanReciprocalBounds =
      Occil.Constants.arctanReciprocalBounds :=
  (Exp.open_lc k e _ arctanReciprocalBounds_lc).symm

@[simp] theorem arctanReciprocalBounds_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.arctanReciprocalBounds : Exp rT) =
      Occil.Constants.arctanReciprocalBounds :=
  Exp.closeRec_fresh x _ k (by simp [arctanReciprocalBounds_fv])

theorem piBounds_lc {rT : Type _} :
    (Occil.Constants.piBounds : Exp rT).IsLocallyClosed := by is_lc

theorem piBounds_fv {rT : Type _} :
    (Occil.Constants.piBounds : Exp rT).fv = ∅ := by
  simp [Occil.Constants.piBounds, Exp.fv, arctanReciprocalBounds_fv]

@[simp] theorem piBounds_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Constants.piBounds = Occil.Constants.piBounds :=
  (Exp.open_lc k e _ piBounds_lc).symm

@[simp] theorem piBounds_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Constants.piBounds : Exp rT) = Occil.Constants.piBounds :=
  Exp.closeRec_fresh x _ k (by simp [piBounds_fv])

private theorem int_beq {rT : Type _} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

private theorem parity (k : ℕ) : ((k : ℤ) % 2 == 0) = decide (k % 2 = 0) := by
  by_cases hp : k % 2 = 0
  · have hp' : (k : ℤ) % 2 = 0 := by omega
    simp [hp, hp']
  · have hp' : (k : ℤ) % 2 ≠ 0 := by omega
    simp [hp, hp']

private theorem termDenominator_source (q k : ℕ) :
    (2 * (k : ℤ) + 1) * (q : ℤ) ^ (2 * k + 1) = termDenominator q k := by
  simp [termDenominator, Nat.cast_add, Nat.cast_mul]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_addTerm (E : CoPset) (q n remaining k : ℕ)
    (hi : k + remaining = n) :
    ⊢ tglWp E
      pl(&(addTermValue (rT := rT) q n).fst #int (k : ℤ)
        #int ((q : ℤ) ^ (2 * k + 1)) #int (numerator q k) #int (denominator q k))
      (fun v : Val rT => iprop(⌜v = encodeTriple (arctanRaw q n)⌝)) := by
  induction remaining generalizing k with
  | zero =>
    have he : k = n := by omega
    subst k
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    twp_pures
    rw [int_beq, beq_self_eq_true]
    twp_pures
    rw [int_beq, parity]
    by_cases hp : n % 2 = 0
    · simp only [hp, decide_true]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [RealEnclosure.encodeTriple, arctanRaw, hp, Exp.ofVal,
        termDenominator_source]
    · simp only [hp, decide_false]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp [RealEnclosure.encodeTriple, arctanRaw, hp, Exp.ofVal,
        termDenominator_source]
  | succ remaining IH =>
    have hne : (k : ℤ) ≠ n := by omega
    have hi' : k + 1 + remaining = n := by omega
    have hrec := IH (k + 1) hi'
    rw [power_succ, numerator_succ, denominator_succ] at hrec
    twp_step
    simp [Exp.open', Exp.openRec, Exp.close, Exp.closeRec, Var.internal.injEq]
    twp_pures
    rw [int_beq, beq_eq_false_iff_ne.mpr hne]
    twp_pures
    rw [int_beq, parity]
    by_cases hp : k % 2 = 0
    · simp only [hp, decide_true]
      iterate 9 twp_pure
      rw [← Nat.cast_add_one, termDenominator_source]
      simp only [sign, hp, ite_true] at hrec
      isimp only [Exp.ofVal]
      iapply hrec
    · simp only [hp, decide_false]
      iterate 9 twp_pure
      rw [← Nat.cast_add_one, termDenominator_source]
      simp only [sign, hp, ite_false] at hrec
      isimp only [Exp.ofVal]
      iapply hrec

/-- The actual alternating-series loop computes the specified integer triple. -/
theorem twp_arctanReciprocalBounds (E : CoPset) (q n : ℕ) (hq : 2 ≤ q)
    (hn : 1 ≤ n) :
    ⊢ tglWp E pl(&Occil.Constants.arctanReciprocalBounds #int (q : ℤ) #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeTriple (arctanRaw q n)⌝)) := by
  have hguard : (decide ((q : ℤ) < 2) || decide ((n : ℤ) ≤ 0)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    omega
  have h := twp_addTerm (rT := rT) (GF := GF) E q n n 0 (Nat.zero_add _)
  simp [addTermValue, addTerm, Exp.close, Exp.closeRec] at h
  iterate 5 twp_pure
  rw [hguard]
  iterate 2 twp_pure
  iapply h

/-- The two checked arctangent calls compute the cross-multiplied Machin bounds. -/
theorem twp_piBounds (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&Occil.Constants.piBounds #int (n : ℤ))
      (fun v : Val rT => iprop(⌜v = encodeTriple (piRaw n)⌝)) := by
  have h5 := twp_arctanReciprocalBounds (rT := rT) (GF := GF) E 5 (n + 1)
    (by decide) (Nat.succ_le_succ (Nat.zero_le _))
  have h239 := twp_arctanReciprocalBounds (rT := rT) (GF := GF) E 239 (n + 1)
    (by decide) (Nat.succ_le_succ (Nat.zero_le _))
  iterate 2 twp_pure
  simp only [arctanReciprocalBounds_openRec, arctanReciprocalBounds_closeRec]
  rw [← Nat.cast_add_one]
  twp_bind_from h5
  iapply tglWp_wand
  isplitl []
  · iapply h5
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  simp only [arctanReciprocalBounds_openRec]
  rw [← Nat.cast_add_one]
  twp_bind_from h239
  iapply tglWp_wand
  isplitl []
  · iapply h239
  iintro %v %hv
  subst v
  twp_pures
  twp_value
  imodintro
  ipureintro
  exact Val.ext rfl

end specification

end SampLib.PiBounds
