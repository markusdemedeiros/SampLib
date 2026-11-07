import SampLib.Discrete.Laws.Zipf
import SampLib.Discrete.UniformFin
import SampLib.Discrete.Support.RationalPowerCoinSyntax
import SampLib.Uniform.RationalCoin
import SampLib.Core.Retry

/-! # Exact finite Zipf rejection

A uniform positive proposal is accepted by the verified reciprocal-power factory.
The finite power sum identifies the target law and its positive acceptance mass.
-/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.Zipf

noncomputable section

private def reciprocalCoin {rT : Type _} (k : ℕ) : Val rT :=
  ⟨pl(fun u, &Occil.rationalCoin #1 #int (k + 1 : ℕ)), .lam (by is_lc), by is_lc⟩

private theorem reciprocal_bias (k : ℕ) :
    RationalCoin.bias 1 (k + 1 : ℕ) (by norm_num) (by positivity) (by omega) =
      reciprocal k := by
  apply Subtype.ext
  simp [RationalCoin.bias, reciprocal]

private def loop {rT : Type _} (n a b : ℕ) : Exp rT := pl%
  rec draw u :=
    let value := #1 + &Occil.uniformInt #int (n : ℤ);
    if &Occil.DiscreteExtra.rationalPowerCoin (fun u, &Occil.rationalCoin #1 value)
        #int (a : ℤ) #int (b : ℤ) #() then value else draw #()

private theorem value_cast (k : ℕ) : (1 : ℤ) + k = ((k + 1 : ℕ) : ℤ) := by omega

private theorem valid_test (n b : ℕ) (hn : 0 < n) (hb : 0 < b) :
    Bool.or (Bool.or (decide ((n : ℤ) ≤ 0)) false)
      (decide ((b : ℤ) ≤ 0)) = false := by
  simp [hn.ne', hb.ne']

attribute [local pl_step_simp]
  RationalPowerCoinSyntax.openRec RationalPowerCoinSyntax.closeRec
  RationalCoin.rationalCoin_openRec RationalCoin.rationalCoin_closeRec
  UniformInt.uniformInt_openRec UniformInt.uniformInt_closeRec

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem reciprocal_spec (E : CoPset) (k : ℕ) :
    IsDistSpec (GF := GF) E pl(&(reciprocalCoin k).fst #())
      (RealCoin.law (reciprocal k)) Val.bool := by
  have h := RationalCoin.rationalCoin_distSpec (rT := rT) (GF := GF) E 1 (k + 1 : ℕ)
    (by norm_num) (by positivity) (by omega)
  rw [reciprocal_bias] at h
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  twp_pure
  iapply h.spec F hF $$ Hcredit

private theorem power_spec (E : CoPset) (n a b : ℕ) (hb : 0 < b) (k : Fin n) :
    IsDistSpec (GF := GF) E
      pl(&Occil.DiscreteExtra.rationalPowerCoin &(reciprocalCoin k).fst
        #int (a : ℤ) #int (b : ℤ) #()) (RealCoin.law (acceptance n a b hb k)) Val.bool :=
  RationalPower.rationalPowerCoin_distSpec E (reciprocal k) a b hb
    (reciprocalCoin k) (reciprocal_spec E k)

omit [ProbLangDist.IsUniformInt rT] in
private abbrev loop_align (E : CoPset) (n a b : ℕ) (Φ : Val rT → IProp GF) := by
  have h : tglWp (rT := rT) (GF := GF) E pl(&(loop n a b) #()) Φ ⊢
      tglWp E pl(&(loop n a b) #()) Φ := BI.BIBase.Entails.refl _
  conv at h =>
    rhs
    simp [loop, Exp.close, Exp.closeRec]
  exact h

private theorem twp_loop (E : CoPset) (n a b : ℕ) [NeZero n] (hb : 0 < b)
    (F : Fin n → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ k, F k ∂law n a b hb) -∗
      tglWp E pl(&(loop n a b) #())
        (fun v : Val rT => iprop(∃ (k : Fin n), ⌜v = Val.int (k + 1 : ℕ)⌝ ∗ ↯ (F k))) := by
  iapply Retry.twp_loop solve_not_value (one_lt_factor n a b hb)
  iintro !> %ε %hε IH Hcredit
  iterate 2 twp_pure
  twp_bind pl(&Occil.uniformInt #int (n : ℤ))
  ihave Hsample := ErrorCredit.weaken (expectation n a b hb F ε) $$ Hcredit
  iapply (UniformFin.uniformFin_distSpec E n).wp (proposalCredit n a b hb F ε)
    (measurable_of_countable _) _ $$ Hsample
  iintro %k Hcredit
  twp_pure
  rw [value_cast]
  twp_pure
  twp_bind pl(&Occil.DiscreteExtra.rationalPowerCoin &(reciprocalCoin k).fst
    #int (a : ℤ) #int (b : ℤ) #())
  isimp only [proposalCredit] at Hcredit
  iapply (power_spec E n a b hb k).wp (coinCredit n a b hb F ε k)
    (measurable_of_countable _) _ $$ Hcredit
  iintro %accepted Hcredit
  cases accepted
  · twp_pure
    isimp only [coinCredit, Bool.false_eq_true, ↓reduceIte] at Hcredit
    iapply loop_align E n a b
      (fun v : Val rT => iprop(∃ (k : Fin n), ⌜v = Val.int (k + 1 : ℕ)⌝ ∗ ↯ (F k)))
    iapply IH $$ Hcredit
  · twp_pure
    twp_value
    imodintro
    iexists k
    isimp only [coinCredit, ↓reduceIte] at Hcredit
    iframe Hcredit
    itrivial

/-- Finite Zipf for every positive bound and nonnegative rational exponent. -/
theorem zipf_distSpec (E : CoPset) (n a b : ℕ) [NeZero n] (hb : 0 < b) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.zipf
      #int (n : ℤ) #int (a : ℤ) #int (b : ℤ)) (law n a b hb)
      (fun k => Val.int (k + 1 : ℕ)) where
  spec F _ := by
    iintro Hcredit
    iterate 8 twp_pure
    rw [valid_test n b (NeZero.pos n) hb]
    iterate 2 twp_pure
    iapply loop_align E n a b
      (fun v : Val rT => iprop(∃ (k : Fin n), ⌜v = Val.int (k + 1 : ℕ)⌝ ∗ ↯ (F k)))
    iapply twp_loop E n a b hb F $$ Hcredit

end specification

end

end SampLib.Zipf
