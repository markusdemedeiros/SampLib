import SampLib.Constants.Laws.ApproximateDigits
import Samplers.Constants.Engines

/-! # Exact coins from approximate radix digits

Uniform digits refine the posterior cell. A fixed finite uncertainty horizon
pays for every unresolved path, including bases with no one-step retry bound.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FromApproximateDigits

noncomputable section

@[simp] private theorem uniform_subst {rT : Type _} (x : Var) (e : Exp rT) :
    Exp.subst Occil.uniformInt x e = Occil.uniformInt :=
  Exp.subst_fresh x _ e (by simp [UniformInt.uniformInt_fv])

private def read {rT : Type _} (D : Model) (oracle : Val rT) : Exp rT :=
  Exp.subst (pl% rec read k digits :=
    let v := &Occil.uniformInt #int (D.base : ℤ);
    let next := digits * #int (D.base : ℤ) + v;
    let pk := source k;
    if pk + #1 <= next then #false else
      if next <= pk - #2 then #true else read (k + #1) next)
    (.named "source") oracle.fst

private theorem base_valid (D : Model) : decide ((D.base : ℤ) < 2) = false :=
  decide_eq_false (by exact_mod_cast not_lt.mpr (Nat.succ_le_of_lt D.atLeastTwo))

private theorem next_position (n : ℕ) : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_round (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ n : ℕ, ⊢ tglWp E pl(&oracle.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (D.approximation n)⌝)))
    (N n : ℕ) (c : ℤ) (F : Bool → ℝ≥0∞)
    (hcontinue : ∀ c : ℤ, ¬D.approximation n + 1 ≤ c → ¬c ≤ D.approximation n - 2 →
      iprop(↯ (D.credit N F (n + 1) c)) ⊢
        tglWp E pl(&(read D oracle) #int ((n + 2 : ℕ) : ℤ) #int c)
          (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) :
    iprop(↯ (D.credit N F n c)) ⊢
      tglWp E pl(&(read D oracle) #int ((n + 1 : ℕ) : ℤ) #int c)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  let _ : NeZero D.base := ⟨D.base_pos.ne'⟩
  iintro Hcredit
  isimp [read, Exp.subst, Exp.close, Exp.closeRec]
  iterate 3 twp_pure
  simp only [UniformInt.uniformInt_openRec]
  twp_bind pl(&Occil.uniformInt #int (D.base : ℤ))
  isimp only [← D.expectation N F n c, ← UniformInt.lintegral_law] at Hcredit
  iapply ((UniformInt.uniformInt_distSpec E D.base).wp
    (fun v => D.credit N F (n + 1) (c * D.base + v))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %j Hcredit
  twp_pures
  twp_bind pl(&oracle.fst #int ((n + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply horacle n
  iintro %v %hv
  subst v
  twp_pures
  by_cases hfalse : D.approximation n + 1 ≤ c * D.base + j
  · rw [decide_eq_true hfalse]
    twp_pures
    twp_value
    imodintro
    iexists false
    ihave Hcredit := ErrorCredit.weaken (D.false_credit N n _ F hfalse) $$ Hcredit
    iframe Hcredit
    itrivial
  · rw [decide_eq_false hfalse]
    twp_pures
    by_cases htrue : c * D.base + j ≤ D.approximation n - 2
    · rw [decide_eq_true htrue]
      twp_pures
      twp_value
      imodintro
      iexists true
      ihave Hcredit := ErrorCredit.weaken (D.true_credit N n _ F htrue) $$ Hcredit
      iframe Hcredit
      itrivial
    · rw [decide_eq_false htrue]
      twp_pure
      twp_pure
      have h := hcontinue (c * D.base + j) hfalse htrue
      simp [read, Exp.subst, Exp.close, Exp.closeRec] at h
      simp only [UniformInt.uniformInt_openRec, Exp.ofVal]
      rw [next_position]
      iapply h $$ Hcredit

private theorem twp_until (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ n : ℕ, ⊢ tglWp E pl(&oracle.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (D.approximation n)⌝)))
    (N n : ℕ) (hn : n ≤ N) (c : ℤ) (F : Bool → ℝ≥0∞) :
    iprop(↯ (D.credit N F n c)) ⊢
      tglWp E pl(&(read D oracle) #int ((n + 1 : ℕ) : ℤ) #int c)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  apply Nat.decreasingInduction (motive := fun n _ => ∀ c : ℤ,
    iprop(↯ (D.credit N F n c)) ⊢
      tglWp E pl(&(read D oracle) #int ((n + 1 : ℕ) : ℤ) #int c)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) ?_ ?_ hn c
  · intro n hn IH c
    iapply twp_round E D oracle horacle N n c F (fun c _ _ => IH c)
  · intro c
    iapply twp_round E D oracle horacle N N c F ?_
    intro c hfalse htrue
    iintro Hcredit
    iexfalso
    iapply ErrorCredit.contradict (D.unresolved_credit N c F hfalse htrue) $$ Hcredit

/-- The certified approximations determine the exact Bernoulli probability. -/
theorem twp_fromApproximateDigits (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ n : ℕ, ⊢ tglWp E pl(&oracle.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (D.approximation n)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit D.probability F) -∗
      tglWp E pl(&Occil.Constants.fromApproximateDigits #int (D.base : ℤ) &oracle.fst #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := D.exists_horizon F δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  twp_pures
  rw [base_valid]
  iterate 2 twp_pure
  have h := twp_until (rT := rT) (GF := GF) E D oracle horacle N 0 (Nat.zero_le _) 0 F
  simp [read, Exp.subst, Exp.close, Exp.closeRec] at h
  simp only [UniformInt.uniformInt_closeRec, UniformInt.uniformInt_openRec]
  iapply h $$ Hcredit

theorem fromApproximateDigits_distSpec (E : CoPset) (D : Model) (oracle : Val rT)
    (horacle : ∀ n : ℕ, ⊢ tglWp E pl(&oracle.fst #int ((n + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (D.approximation n)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.fromApproximateDigits #int (D.base : ℤ) &oracle.fst #())
      (RealCoin.law D.probability) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_fromApproximateDigits E D oracle horacle F)

end specification

end

end SampLib.FromApproximateDigits
