import SampLib.Discrete.Laws.NegativeBinomialShape
import SampLib.Discrete.NegativeBinomial
import SampLib.Uniform.RationalCoin
import SampLib.Core.Syntax.ClosedExp
import Samplers.Discrete.Counts

/-! # Rational-shape negative binomial by rejection from the ceiling shape

The proposal is the integer negative binomial with shape `M = ⌈A/B⌉`. A count `k`
is accepted with the rising-product ratio `∏_{i<k} (A + iB) / ((M + i)B)`, which
cancels the proposal's multichoose coefficient. The accepted-proposal identity
preserves arbitrary continuation credits and pays for the retry amplification.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PolyaRational

noncomputable section

open PolyaEggenberger (rising)

/-- The source's integer ceiling of the target shape `A/B`. -/
def ceiling (A B : ℕ) : ℕ := (A + B - 1) / B

theorem ceiling_pos (A B : ℕ) (hA : 0 < A) (hB : 0 < B) : 0 < ceiling A B :=
  Nat.div_pos (by omega) hB

theorem le_ceiling (A B : ℕ) (hB : 0 < B) : A ≤ ceiling A B * B := by
  have h := Nat.lt_div_mul_add (a := A + B - 1) hB
  unfold ceiling
  omega

def shape (A B : ℕ) : ℝ := (A : ℝ) / B

theorem shape_pos (A B : ℕ) (hA : 0 < A) (hB : 0 < B) : 0 < shape A B := by
  unfold shape
  positivity

theorem shape_le (A B : ℕ) (hB : 0 < B) : shape A B ≤ ceiling A B := by
  unfold shape
  rw [div_le_iff₀ (by exact_mod_cast hB)]
  exact_mod_cast le_ceiling A B hB

/-- The success probability `s/t` of every proposal trial. -/
abbrev success (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) : unitInterval :=
  RationalCoin.bias s t (by omega) (by omega) (by exact_mod_cast hst)

theorem success_pos (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) : 0 < (success s t hs hst : ℝ) := by
  simp only [success, RationalCoin.bias, Int.cast_natCast]
  exact div_pos (by exact_mod_cast hs) (by exact_mod_cast lt_of_lt_of_le hs hst)

/-- The canonical negative binomial with shape `A/B` and success probability `s/t`. -/
abbrev law (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hst : s ≤ t) :=
  NegativeBinomialShape.law (shape A B) (shape_pos A B hA hB) (success s t hs hst)
    (success_pos s t hs hst)

section mathematics

open MeasureTheory

variable (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hst : s ≤ t)

abbrev acceptance : ℕ → unitInterval :=
  NegativeBinomialShape.acceptance (shape A B) (shape_pos A B hA hB) (ceiling A B)
    (ceiling_pos A B hA hB) (shape_le A B hB)

abbrev proposal : Measure ℕ := NegativeBinomial.law (success s t hs hst) (ceiling A B)

theorem mass_ne_zero :
    AcceptedProposal.mass (proposal A B s t hs hst) (acceptance A B hA hB) ≠ 0 :=
  NegativeBinomialShape.accepted_mass_ne_zero _ _ _ (success_pos s t hs hst) _ _ _

/-- Accept the proposed count or retain the amplified retry budget. -/
def branchCredit (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) (accepted : Bool) : ℝ≥0∞ :=
  if accepted then F k else
    (∫⁻ n, F n ∂law A B s t hA hB hs hst) +
      AcceptedProposal.factor (proposal A B s t hs hst) (acceptance A B hA hB) * ε

/-- Conditional expectation of the rising-product acceptance coin. -/
def proposalCredit (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  RealCoin.credit (acceptance A B hA hB k) (branchCredit A B s t hA hB hs hst F ε k)

/-- Rising-product weighting preserves the target expectation and the retry slack. -/
theorem expectation_preservation (F : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∫⁻ k, proposalCredit A B s t hA hB hs hst F ε k ∂proposal A B s t hs hst) ≤
      (∫⁻ n, F n ∂law A B s t hA hB hs hst) + ε := by
  have hC : AcceptedProposal.credit (proposal A B s t hs hst) (acceptance A B hA hB)
      (mass_ne_zero A B s t hA hB hs hst) F = ∫⁻ n, F n ∂law A B s t hA hB hs hst := by
    rw [AcceptedProposal.credit, NegativeBinomialShape.accepted_law_eq]
  simpa only [proposalCredit, branchCredit, RealCoin.credit, RealCoin.pmf,
    ite_true, Bool.false_eq_true, ite_false, AcceptedProposal.kernel,
    AcceptedProposal.weight, AcceptedProposal.rejectedWeight, hC] using
    AcceptedProposal.expectation_preservation (proposal A B s t hs hst)
      (acceptance A B hA hB) (measurable_of_countable _)
      (mass_ne_zero A B s t hA hB hs hst) F (measurable_of_countable _) ε

include hA hB in
theorem bottom_pos (k : ℕ) : (0 : ℤ) < rising (ceiling A B * B) B k := by
  exact_mod_cast NegativeBinomialShape.rising_pos (Nat.mul_pos (ceiling_pos A B hA hB) hB) B k

include hB in
theorem top_le (k : ℕ) : (rising A B k : ℤ) ≤ rising (ceiling A B * B) B k := by
  exact_mod_cast NegativeBinomialShape.rising_mono (le_ceiling A B hB) B k

/-- The source's integer products give exactly the acceptance probability. -/
theorem ratio_bias (k : ℕ) :
    RationalCoin.bias (rising A B k) (rising (ceiling A B * B) B k) (by positivity)
      (bottom_pos A B hA hB k) (top_le A B hB k) = acceptance A B hA hB k := by
  apply Subtype.ext
  simp only [RationalCoin.bias, Int.cast_natCast, NegativeBinomialShape.acceptance]
  rw [NegativeBinomialShape.rising_ratio_eq A B (ceiling A B) k hB (ceiling_pos A B hA hB)]
  rfl

end mathematics

private theorem top_step (A B j : ℕ) :
    (rising A B j : ℤ) * ((A : ℤ) + (j : ℤ) * B) = (rising A B (j + 1) : ℕ) := by
  rw [NegativeBinomialShape.rising_succ_right]
  push_cast
  ring

private theorem bottom_step (M B j : ℕ) :
    (rising (M * B) B j : ℤ) * (((M : ℤ) + j) * B) = (rising (M * B) B (j + 1) : ℕ) := by
  rw [NegativeBinomialShape.rising_succ_right]
  push_cast
  ring

private theorem index_test {rT : Type _} [BEq rT] (j k : ℕ) :
    ((BaseLit.int (j : ℤ) : BaseLit rT) == .int (k : ℤ)) = decide (j = k) := by
  change decide ((j : ℤ) = k) = _
  exact decide_eq_decide.mpr (by omega)

/-- The source's deterministic product recursion, with its count and shape fixed. -/
private def products {rT : Type _} (A B M k : ℕ) : Exp rT := pl%
  rec build i top bottom :=
    if i = #int (k : ℤ) then (top, bottom) else
      build (i + #1) (top * (#int (A : ℤ) + i * #int (B : ℤ)))
        (bottom * ((#int (M : ℤ) + i) * #int (B : ℤ)))

private def coin {rT : Type _} (s t : ℕ) : Val rT :=
  ⟨.lam pl(&Occil.rationalCoin #int (s : ℤ) #int (t : ℤ)), .lam (by is_lc), by is_lc⟩

private instance rational_closed {rT : Type _} : ClosedExp (Occil.rationalCoin : Exp rT) where
  lc := by is_lc
  fv := RationalCoin.rationalCoin_fv

private instance negativeBinomial_closed {rT : Type _} :
    ClosedExp (Occil.negativeBinomial : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.negativeBinomial, Occil.geometric, Exp.fv]

private theorem negativeBinomial_openRec {rT : Type _} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.negativeBinomial = Occil.negativeBinomial := ClosedExp.openRec k e

private theorem negativeBinomial_closeRec {rT : Type _} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.negativeBinomial : Exp rT) = Occil.negativeBinomial :=
  ClosedExp.closeRec k x

attribute [local pl_step_simp] RationalCoin.rationalCoin_openRec
  RationalCoin.rationalCoin_closeRec negativeBinomial_openRec negativeBinomial_closeRec

private instance coin_closed {rT : Type _} (s t : ℕ) : ClosedExp ((coin s t : Val rT).fst) where
  lc := by is_lc
  fv := by simp [coin, Exp.fv, RationalCoin.rationalCoin_fv]

/-- The source's retry loop after its parameters and ceiling are substituted. -/
private def loop {rT : Type _} (A B s t : ℕ) : Exp rT := pl%
  rec draw u :=
    let value := &Occil.negativeBinomial &(coin s t).fst #int (ceiling A B : ℤ);
    let products := (rec build i top bottom :=
      if i = value then (top, bottom) else
        build (i + #1) (top * (#int (A : ℤ) + i * #int (B : ℤ)))
          (bottom * ((#int (ceiling A B : ℤ) + i) * #int (B : ℤ))));
    let ratio := products #0 #1 #1;
    if &Occil.rationalCoin (fst(ratio)) (snd(ratio)) then value else draw #()

private theorem valid_test (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hst : s ≤ t) :
    Bool.or (Bool.or (Bool.or (decide ((A : ℤ) ≤ 0)) (decide ((B : ℤ) ≤ 0)))
      (decide ((s : ℤ) ≤ 0))) (decide ((t : ℤ) < s)) = false := by
  simp [hA.ne', hB.ne', hs.ne', hst]

private theorem ceiling_cast (A B : ℕ) (hA : 0 < A) :
    ((A : ℤ) + B - 1) / B = ((ceiling A B : ℕ) : ℤ) := by
  have h : (A : ℤ) + B - 1 = ((A + B - 1 : ℕ) : ℤ) := by omega
  rw [h, ← Int.natCast_ediv, ceiling]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- From step `j`, the recursion returns both rising products at the proposed count `k`. -/
private theorem twp_products (E : CoPset) (A B M d j : ℕ) (Φ : Val rT → IProp GF) :
    Φ (Val.pair (Val.int (rising A B (j + d) : ℕ)) (Val.int (rising (M * B) B (j + d) : ℕ))) ⊢
      tglWp E pl(&(products A B M (j + d)) #int (j : ℤ) #int ((rising A B j : ℕ) : ℤ)
        #int ((rising (M * B) B j : ℕ) : ℤ)) Φ := by
  induction d generalizing j with
  | zero =>
    iintro H
    twp_pures
    rw [index_test, decide_eq_true (Nat.add_zero j).symm]
    twp_pures
    twp_value
    imodintro
    iexact H
  | succ d ih =>
    iintro H
    twp_pures
    rw [index_test, decide_eq_false (by omega : j ≠ j + (d + 1))]
    iterate 8 twp_pure
    rw [top_step, bottom_step, ← Nat.cast_add_one, show j + (d + 1) = j + 1 + d by omega]
    ieval (
      change _ ⊢ tglWp E pl(&(products A B M (j + 1 + d)) #int ((j + 1 : ℕ) : ℤ)
        #int ((rising A B (j + 1) : ℕ) : ℤ) #int ((rising (M * B) B (j + 1) : ℕ) : ℤ)) Φ)
    iapply ih (j + 1) $$ H

omit [ProbLangDist.IsUniformInt rT] in
/-- The source's initial call `products 0 1 1` returns both rising products at `k`. -/
private theorem twp_products_start (E : CoPset) (A B M k : ℕ) (Φ : Val rT → IProp GF) :
    Φ (Val.pair (Val.int (rising A B k : ℕ)) (Val.int (rising (M * B) B k : ℕ))) ⊢
      tglWp E pl(&(products A B M k) #0 #1 #1) Φ := by
  have h := twp_products E A B M k 0 Φ
  rw [Nat.zero_add] at h
  exact h

private theorem coin_spec (E : CoPset) (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) :
    IsDistSpec (GF := GF) E pl(&(coin (rT := rT) s t).fst #())
      (RealCoin.law (success s t hs hst)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_pure
    iapply (RationalCoin.rationalCoin_distSpec E s t _ _ _).spec F hF $$ Hcredit

private theorem acceptance_spec (E : CoPset) (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (k : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.rationalCoin #int ((rising A B k : ℕ) : ℤ)
      #int ((rising (ceiling A B * B) B k : ℕ) : ℤ))
      (RealCoin.law (acceptance A B hA hB k)) Val.bool := by
  rw [← ratio_bias A B hA hB k]
  exact RationalCoin.rationalCoin_distSpec E _ _ _ _ _

omit [ProbLangDist.IsUniformInt rT] in
private abbrev loop_align (E : CoPset) (A B s t : ℕ) (Φ : Val rT → IProp GF) := by
  have h : tglWp (rT := rT) (GF := GF) E pl(&(loop A B s t) #()) Φ ⊢
      tglWp E pl(&(loop A B s t) #()) Φ := BI.BIBase.Entails.refl _
  conv at h =>
    rhs
    simp [loop, Exp.close, Exp.closeRec, ClosedExp.closeRec]
  exact h

omit [ProbLangDist.IsUniformInt rT] in
private abbrev source_align (E : CoPset) (A B s t : ℕ) (Φ : Val rT → IProp GF) := by
  have h := loop_align (rT := rT) (GF := GF) E A B s t Φ
  conv at h =>
    rhs
    simp [coin, Exp.close, Exp.closeRec]
  exact h

private theorem twp_loop (E : CoPset) (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hst : s ≤ t) (F : ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ n, F n ∂law A B s t hA hB hs hst) -∗ tglWp E pl(&(loop A B s t) #())
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  have hnb := NegativeBinomial.negativeBinomial_distSpec (rT := rT) (GF := GF) E
    (success s t hs hst) (coin s t) (coin_spec E s t hs hst) (ceiling A B)
    (Or.inr (success_pos s t hs hst))
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε
    (AcceptedProposal.one_lt_factor _ _ (mass_ne_zero A B s t hA hB hs hst)) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  iterate 2 twp_pure
  simp only [ClosedExp.openRec, ClosedExp.closeRec]
  twp_bind pl(&Occil.negativeBinomial &(coin s t).fst #int (ceiling A B : ℤ))
  icombine Hcredit Hterm as Hcredit
  ihave Hcredit := ErrorCredit.weaken
    (expectation_preservation A B s t hA hB hs hst F ε) $$ Hcredit
  iapply (hnb.wp (proposalCredit A B s t hA hB hs hst F ε) (measurable_of_countable _) _)
    $$ Hcredit
  iintro %k Hcredit
  iterate 2 twp_pure
  twp_bind pl(&(products A B (ceiling A B) k) #0 #1 #1)
  iapply twp_products_start
  iterate 3 twp_pure
  twp_bind pl(&Occil.rationalCoin #int ((rising A B k : ℕ) : ℤ)
    #int ((rising (ceiling A B * B) B k : ℕ) : ℤ))
  isimp only [proposalCredit, ← RealCoin.lintegral_law] at Hcredit
  iapply ((acceptance_spec E A B hA hB k).wp (branchCredit A B s t hA hB hs hst F ε k)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %accepted Hcredit
  cases accepted
  · twp_pure
    isimp only [branchCredit, Bool.false_eq_true, ite_false] at Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    iapply loop_align E A B s t
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n)))
    iapply IH $$ Hterm Hcredit
  · twp_pure
    twp_value
    imodintro
    iexists k
    isimp only [branchCredit, ite_true] at Hcredit
    iframe Hcredit
    itrivial

/-- Exact rational-shape negative binomial on its complete valid parameter domain. -/
theorem polyaRational_distSpec (E : CoPset) (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hs : 0 < s) (hst : s ≤ t) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.polyaRational
      #int (A : ℤ) #int (B : ℤ) #int (s : ℤ) #int (t : ℤ))
      (law A B s t hA hB hs hst) (fun n : ℕ => Val.int (n : ℤ)) where
  spec F _ := by
    iintro Hcredit
    twp_pures
    rw [valid_test A B s t hA hB hs hst]
    iterate 6 twp_pure
    rw [ceiling_cast A B hA]
    iapply source_align E A B s t
      (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n)))
    iapply twp_loop E A B s t hA hB hs hst F $$ Hcredit

end specification

end

end SampLib.PolyaRational
