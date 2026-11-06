import SampLib.HanHoshi

/-! # Exact categorical sampling by Han–Hoshi interval refinement -/

open ProbLang
open scoped ENNReal

namespace SampLib.HanHoshi

noncomputable section

private theorem accepted_test (i : ℕ) : decide ((0 : ℤ) ≤ i) = true :=
  decide_eq_true (Int.natCast_nonneg i)

private theorem bit_symbol (b : ℤ) (hb : 0 ≤ b ∧ b < 2) :
    (if decide (b.toNat = 1) then 1 else 0 : ℤ) = b := by
  by_cases h : b.toNat = 1
  · simp only [h, decide_true, ite_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

private theorem prefix_step (p : List Bool) (b : ℤ) (hb : 0 ≤ b ∧ b < 2) :
    UniformBag.rank p * 2 + b = UniformBag.rank (p ++ [decide (b.toNat = 1)]) := by
  rw [LatentDigits.rank_extend, bit_symbol b hb]

private theorem denominator_step (p : List Bool) (b : Bool) :
    (((2 ^ p.length : ℕ) : ℤ) * 2) = ((2 ^ (p ++ [b]).length : ℕ) : ℤ) := by
  simp only [List.length_append, List.length_singleton, pow_succ, Nat.cast_mul, Nat.cast_ofNat]

private theorem remaining_step (p : List Bool) (b : Bool) (T N : ℕ)
    (h : p.length + (T + 1) = N) : (p ++ [b]).length + T = N := by
  simp only [List.length_append, List.length_singleton]
  omega

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open scoped SampLib.HanHoshi.Program

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec Program.weights_closeRec

/-- A fresh fair bit refines the same latent uniform and preserves its conditional credit. -/
private theorem twp_refine (E : CoPset) (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ)
    (F : ℤ → ℝ≥0∞) (p : List Bool)
    (hrec : ∀ b : Bool,
      ⊢ ↯ (DyadicPosterior.credit (p ++ [b]) (horizonCredit ws ht N F)) -∗
        tglWp E pl(&(Program.loop ws (ws.sum : ℤ))
          #int (UniformBag.rank (p ++ [b])) #int ((2 ^ (p ++ [b]).length : ℕ) : ℤ))
          (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i)))) :
    ⊢ ↯ (DyadicPosterior.credit p (horizonCredit ws ht N F)) -∗
      tglWp E (Program.refine ws (ws.sum : ℤ) (UniformBag.rank p) ((2 ^ p.length : ℕ) : ℤ))
        (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  twp_pure
  twp_bind pl(rand(#2, #()))
  iapply (twp_rand_exp
    (ε₂ := fun b => DyadicPosterior.credit (p ++ [decide (b = 1)]) (horizonCredit ws ht N F))
    (by decide) (bit_expectation ws ht N F p).le) $$ Hcredit
  iintro %b ⟨%hb, Hcredit⟩
  twp_pure
  simp only [Exp.ofVal]
  twp_pure
  rw [prefix_step p b hb, denominator_step p (decide (b.toNat = 1))]
  isimp only [Exp.ofVal]
  iapply hrec (decide (b.toNat = 1)) $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
/-- The scan returns a certified label or continues with a smaller dyadic cell. -/
private theorem twp_round (E : CoPset) (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ)
    (F : ℤ → ℝ≥0∞) (p : List Bool)
    (hcontinue : scan ws.sum (UniformBag.rank p).toNat (2 ^ p.length) ws 0 = none →
      ⊢ ↯ (DyadicPosterior.credit p (horizonCredit ws ht N F)) -∗
        tglWp E (Program.refine ws (ws.sum : ℤ) (UniformBag.rank p) ((2 ^ p.length : ℕ) : ℤ))
          (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i)))) :
    ⊢ ↯ (DyadicPosterior.credit p (horizonCredit ws ht N F)) -∗
      tglWp E pl(&(Program.loop ws (ws.sum : ℤ))
        #int (UniformBag.rank p) #int ((2 ^ p.length : ℕ) : ℤ))
        (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  iterate 3 twp_pure
  twp_bind pl(&(Program.find (ws.sum : ℤ))
    &(listVal (fun n : ℕ => Val.int n) ws).fst #0 #int (UniformBag.rank p)
    #int ((2 ^ p.length : ℕ) : ℤ) #0)
  iapply tglWp_wand
  isplitl []
  · have hfind := twp_find (rT := rT) (GF := GF) E ws.sum (UniformBag.rank p).toNat
      (2 ^ p.length) ws 0 0
    simp only [Int.toNat_of_nonneg (rank_bounds p).1, Nat.cast_zero] at hfind
    iapply hfind
  iintro %v %hv
  subst v
  iterate 2 twp_pure
  cases hs : scan ws.sum (UniformBag.rank p).toNat (2 ^ p.length) ws 0 with
  | some i =>
    simp only [scanResult, zero_add]
    rw [accepted_test i]
    twp_pures
    twp_value
    imodintro
    iexists (i : ℤ)
    isplit
    · ipureintro
      rfl
    iapply ErrorCredit.weaken (return_credit ws ht N F p i hs) $$ Hcredit
  | none =>
    simp only [scanResult]
    twp_pure
    iapply hcontinue hs $$ Hcredit

/-- A chosen horizon either certifies a cell or spends one impossible error credit. -/
private theorem twp_horizon (E : CoPset) (ws : List ℕ) (ht : 0 < ws.sum) (N : ℕ)
    (F : ℤ → ℝ≥0∞) (T : ℕ) (p : List Bool) (hlen : p.length + T = N) :
    ⊢ ↯ (DyadicPosterior.credit p (horizonCredit ws ht N F)) -∗
      tglWp E pl(&(Program.loop ws (ws.sum : ℤ))
        #int (UniformBag.rank p) #int ((2 ^ p.length : ℕ) : ℤ))
        (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i))) := by
  induction T generalizing p with
  | zero =>
    refine twp_round E ws ht N F p ?_
    intro hnone
    iintro Hcredit
    iexfalso
    iapply ErrorCredit.contradict (unresolved_credit ws ht N F p
      (by simpa only [Nat.add_zero] using hlen) hnone) $$ Hcredit
  | succ T ih =>
    refine twp_round E ws ht N F p ?_
    intro _
    exact twp_refine E ws ht N F p (fun b => ih (p ++ [b]) (remaining_step p b T N hlen))

attribute [local pl_step_simp] WeightedValidation.validWeights_openRec
  WeightedValidation.validWeights_closeRec WeightedValidation.sumInts_openRec
  WeightedValidation.sumInts_closeRec

/-- Dyadic whole-cell refinement samples the exact categorical law, including zero weights. -/
theorem twp_hanHoshi (E : CoPset) (ws : List ℕ) (ht : 0 < ws.sum) (F : ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ i, F i ∂CategoricalCDF.law ws) -∗
      tglWp E pl(&Occil.Weighted.hanHoshi
        &(listVal (fun n : ℕ => Val.int n) ws).fst #())
        (fun v => iprop(∃ i : ℤ, ⌜v = Val.int i⌝ ∗ ↯ (F i))) := by
  iintro Hcredit
  iapply Program.twp_open E ws
  twp_bind pl(&Occil.Weighted.validWeights &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedValidation.twp_validWeights E ws ht
  iintro %v %hv
  subst v
  twp_pure
  twp_bind pl(&Occil.sumInts &(listVal (fun n : ℕ => Val.int n) ws).fst)
  iapply tglWp_wand
  isplitl []
  · iapply WeightedChoice.twp_sumInts E ws
  iintro %v %hv
  subst v
  iterate 3 twp_pure
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hbudget⟩ := exists_horizon ws ht F δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hbudget $$ Htotal
  have hloop := twp_horizon (rT := rT) (GF := GF) E ws ht N F N [] (Nat.zero_add N)
  simp only [UniformBag.rank, List.length_nil, pow_zero, Nat.cast_one] at hloop
  iapply hloop $$ Hcredit

/-- A compositional specification for every positive-total natural-weight vector. -/
theorem hanHoshi_distSpec (E : CoPset) (ws : List ℕ) [NeZero ws.sum] :
    IsDistSpec (GF := GF) E pl(&Occil.Weighted.hanHoshi
      &(listVal (fun n : ℕ => Val.int n) ws).fst #()) (CategoricalCDF.law ws) Val.int where
  spec F _ := wand_entails (twp_hanHoshi E ws (NeZero.pos ws.sum) F)

end specification

end

end SampLib.HanHoshi
