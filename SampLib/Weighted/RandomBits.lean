import SampLib.Weighted.Laws.RandomBits
import SampLib.Uniform.UniformInt
import Samplers.Weighted.Uniform

/-! # Uniform words from independent bits

After reading `n` bits, a prefix `v` is followed by a uniform suffix of width `2^n`.
-/

open ProbLang Finset
open scoped ENNReal

namespace SampLib.RandomBits

noncomputable section

private theorem prefix_cast (v : ℕ) (b : ℤ) (hb : 0 ≤ b) :
    (v : ℤ) * 2 + b = ((v * 2 + b.toNat : ℕ) : ℤ) := by
  simp [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hb]

theorem randomBits_lc {rT : Type _} :
    (Occil.Weighted.randomBits : Exp rT).IsLocallyClosed := by is_lc

theorem randomBits_fv {rT : Type _} :
    (Occil.Weighted.randomBits : Exp rT).fv = ∅ := by
  simp [Occil.Weighted.randomBits, Exp.fv]

@[simp] theorem randomBits_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.Weighted.randomBits = Occil.Weighted.randomBits :=
  (Exp.open_lc k e _ randomBits_lc).symm

@[simp] theorem randomBits_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.Weighted.randomBits : Exp rT) = Occil.Weighted.randomBits :=
  Exp.closeRec_fresh x _ k (by simp [randomBits_fv])

private def loop {rT : Type _} : Exp rT := pl%
  rec read remaining value :=
    if remaining = #0 then value else
      read (remaining - #1) (value * #2 + rand(#2, #()))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (n v : ℕ) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (credit n v F) -∗
      tglWp E pl(&loop #int (n : ℤ) #int (v : ℤ))
        (fun result : Val rT => iprop(∃ k : ℕ,
          ⌜result = Val.int (k : ℤ)⌝ ∗ ↯ (F k))) := by
  induction n generalizing v with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists v
    isimp only [credit_zero] at Hcredit
    iframe Hcredit
    itrivial
  | succ n ih =>
    iintro Hcredit
    twp_pures
    twp_bind pl(rand(#2, #()))
    iapply (twp_rand_exp (ε₂ := fun b => credit n (v * 2 + b) F) (by norm_num) ?_)
      $$ Hcredit
    · exact le_of_eq (expectation n v F)
    iintro %b ⟨%hb, Hcredit⟩
    twp_pure
    simp only [Exp.ofVal]
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    rw [prefix_cast v b hb.1]
    have hrec := ih (v * 2 + b.toNat)
    simp [loop, Exp.close, Exp.closeRec, max_eq_left hb.1] at hrec
    isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Int.toNat_of_nonneg hb.1]
    iapply hrec $$ Hcredit

/-- Every binary word, including the empty word, has the uniform integer law. -/
theorem randomBits_distSpec (E : CoPset) (n : ℕ) :
    letI : NeZero (2 ^ n) := ⟨by positivity⟩
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.randomBits #int (n : ℤ))
      (UniformInt.law (2 ^ n)) (fun k : ℕ => Val.int (k : ℤ)) := by
  refine ⟨fun F _ => ?_⟩
  have hloop := twp_loop (rT := rT) (GF := GF) E n 0 F
  simp [loop, Exp.close, Exp.closeRec] at hloop
  iintro Hcredit
  iterate 4 twp_pure
  iapply hloop
  isimp only [UniformInt.lintegral_law, Nat.cast_pow, Nat.cast_ofNat] at Hcredit
  isimp only [credit, Nat.zero_mul, Nat.zero_add]
  iexact Hcredit

end specification

end

end SampLib.RandomBits
