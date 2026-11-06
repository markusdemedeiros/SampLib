import SampLib.Common.Laws.Binomial

/-! # A finite-support gateway for abstract binomial callbacks

The count is bounded by the number of trials. Impossible counts carry infinite
credit, so the gateway remains valid for arbitrary extended-real continuations.
-/

open ProbLang MeasureTheory Finset
open scoped ENNReal

namespace SampLib.BinomialFinite

noncomputable section

def pmf (p : unitInterval) (n : ℕ) (k : Fin (n + 1)) : ℝ≥0∞ :=
  ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ (k : ℕ) * (1 - (p : ℝ)) ^ (n - k))

def encode {rT : Type} {n : ℕ} (k : Fin (n + 1)) : Val rT :=
  Val.int ((k : ℕ) : ℤ)

def extend {n : ℕ} (fallback : ℝ≥0∞) (F : Fin (n + 1) → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  if h : k ≤ n then F ⟨k, Nat.lt_succ_iff.mpr h⟩ else fallback

theorem expectation (p : unitInterval) (n : ℕ) (fallback : ℝ≥0∞)
    (F : Fin (n + 1) → ℝ≥0∞) :
    (∫⁻ k, extend fallback F k ∂Binomial.law p n) = ∑ k, pmf p n k * F k := by
  rw [Binomial.lintegral_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun k =>
      ENNReal.ofReal ((n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)) *
        extend fallback F k) (n + 1)]
  apply sum_congr rfl
  intro k _
  simp only [extend, dite_eq_left (Nat.le_of_lt_succ k.isLt), pmf]

theorem pmf_sum (p : unitInterval) (n : ℕ) : ∑ k, pmf p n k = 1 := by
  have h := expectation p n 1 (fun _ => 1)
  simpa [extend] using h.symm

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- The finite count is part of the postcondition, including deterministic endpoint coins. -/
theorem twp_binomial (E : CoPset) (p : unitInterval) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (n : ℕ) (F : Fin (n + 1) → ℝ≥0∞) :
    ⊢ ↯ (∑ k, pmf p n k * F k) -∗
      tglWp E pl(&Occil.binomial &coin.fst #int (n : ℤ))
        (fun v : Val rT => BIBase.exists (fun k : Fin (n + 1) =>
          BIBase.sep (BIBase.pure (v = encode k)) (↯ (F k)))) := by
  have ht := Binomial.twp_binomial (rT := rT) (GF := GF) E p coin hcoin n (extend ∞ F)
  rw [expectation] at ht
  iintro Hcredit
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply ht $$ Hcredit
  iintro %v ⟨%k, %hv, Hcredit⟩
  by_cases hk : k ≤ n
  · isimp only [extend, dite_eq_left hk] at Hcredit
    iexists ⟨k, Nat.lt_succ_iff.mpr hk⟩
    iframe Hcredit
    ipureintro
    exact hv
  · isimp only [extend, dite_eq_right hk] at Hcredit
    iexfalso
    iapply ErrorCredit.contradict (show (1 : ℝ≥0∞) ≤ ∞ from le_top) $$ Hcredit

end specification

end

end SampLib.BinomialFinite
