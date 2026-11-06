import SampLib.Distributions.Digits
import SampLib.Samplers.RealCoin
import SampLib.Samplers.UniformInt
import Samplers.Constants.Engines

/-! # Comparing a uniform digit stream with a fixed expansion

Equal digits retry. The retry probability is `1/base`, uniformly at most one half,
including the all-zero and all-maximal expansions of the interval endpoints.
-/

open ProbLang Finset
open ENNReal (ofReal)
open scoped ENNReal

namespace SampLib.FromDigits

noncomputable section

/-- The probability represented by the expansion beginning at position `k`. -/
def bias {b : ℕ} (d : ℕ → Fin b) (k : ℕ) : unitInterval :=
  ⟨Real.ofDigits (fun n => d (k + n)), Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

private theorem bias_cons {b : ℕ} (d : ℕ → Fin b) (k : ℕ) :
    (bias d k : ℝ) = ((d k : ℝ) + (bias d (k + 1) : ℝ)) / b := by
  simpa [bias, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    Real.ofDigits_cons (fun n => d (k + n))

/-- A differing digit decides; an equal digit retains the tail expectation. -/
def rankCredit {b : ℕ} (d : ℕ → Fin b) (k : ℕ) (F : Bool → ℝ≥0∞)
    (ε : ℝ≥0∞) (v : ℕ) : ℝ≥0∞ :=
  if v < d k then F true else if d k < v then F false
  else RealCoin.credit (bias d (k + 1)) F + 2 * ε

/-- Partitioning the ranks below, at, and above the fixed digit conserves credit. -/
theorem expectation {b : ℕ} (hb : 1 < b) (d : ℕ → Fin b) (k : ℕ)
    (F : Bool → ℝ≥0∞) (ε : ℝ≥0∞) :
    (∑ v ∈ range b, rankCredit d k F ε v) / b ≤ RealCoin.credit (bias d k) F + ε := by
  have hd := (d k).isLt
  have hbR : (0 : ℝ) < b := by positivity
  have hparts : b = (d k).val + 1 + (b - ((d k).val + 1)) := by omega
  have hsum : (∑ v ∈ range b, rankCredit d k F ε v) =
      (d k : ℝ≥0∞) * F true + RealCoin.credit (bias d (k + 1)) F +
        ((b - ((d k).val + 1) : ℕ) : ℝ≥0∞) * F false + 2 * ε := by
    rw [show range b = range ((d k).val + 1 + (b - ((d k).val + 1))) from
      congrArg range hparts]
    rw [sum_range_add, sum_range_add]
    have hleft : (∑ v ∈ range (d k).val, rankCredit d k F ε v) =
        (d k : ℝ≥0∞) * F true := by
      simp only [rankCredit]
      calc
        _ = ∑ v ∈ range (d k).val, F true :=
          sum_congr rfl fun v hv => ite_eq_left (mem_range.mp hv)
        _ = _ := by simp [nsmul_eq_mul]
    rw [hleft]
    simp only [sum_range_one, Nat.add_zero, rankCredit, lt_self_iff_false, ite_false]
    have hright : (∑ v ∈ range (b - ((d k).val + 1)),
        rankCredit d k F ε ((d k).val + 1 + v)) =
        ((b - ((d k).val + 1) : ℕ) : ℝ≥0∞) * F false := by
      simp [rankCredit, show ∀ v : ℕ, ¬(d k).val + 1 + v < (d k).val by omega,
        show ∀ v : ℕ, (d k).val < (d k).val + 1 + v by omega, nsmul_eq_mul]
    simp only [rankCredit] at hright
    rw [hright]
    ring
  have ht : ofReal (bias d k : ℝ) =
      ((d k : ℝ≥0∞) + ofReal (bias d (k + 1) : ℝ)) / b := by
    rw [bias_cons, ENNReal.ofReal_div_of_pos hbR,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (bias d (k + 1)).2.1]
    simp
  have hc : 1 - (bias d k : ℝ) =
      (((b - ((d k).val + 1) : ℕ) : ℝ) + (1 - (bias d (k + 1) : ℝ))) / b := by
    rw [bias_cons, Nat.cast_sub (by omega : (d k).val + 1 ≤ b)]
    push_cast
    field_simp
    ring
  have hf : ofReal (1 - (bias d k : ℝ)) =
      (((b - ((d k).val + 1) : ℕ) : ℝ≥0∞) +
        ofReal (1 - (bias d (k + 1) : ℝ))) / b := by
    rw [hc, ENNReal.ofReal_div_of_pos hbR,
      ENNReal.ofReal_add (Nat.cast_nonneg _) (sub_nonneg.mpr (bias d (k + 1)).2.2)]
    simp only [ENNReal.ofReal_natCast]
  have hamp : (2 : ℝ≥0∞) / b ≤ 1 := by
    rw [ENNReal.div_le_iff (by positivity : (b : ℝ≥0∞) ≠ 0) (by finiteness)]
    norm_cast
    omega
  calc
    _ = RealCoin.credit (bias d k) F + (2 / b) * ε := by
      rw [hsum]
      simp only [RealCoin.credit, RealCoin.pmf, ite_true, Bool.false_eq_true, ite_false, ht, hf,
        ENNReal.div_eq_inv_mul]
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hamp)

/-- The recursive body is assembled structurally to preserve callback free variables. -/
private def read {rT : Type _} (b : ℕ) (digit : Val rT) : Exp rT :=
  .fix (.lam (.app (.lam
    (.cond (.binop .or (.binop .lt (.bvar 0) (.lit (.int 0)))
      (.binop .le (.lit (.int b)) (.bvar 0))) .fail
      (.app (.lam
        (.cond (.binop .lt (.bvar 0) (.bvar 1)) (.lit (.bool true))
          (.cond (.binop .lt (.bvar 1) (.bvar 0)) (.lit (.bool false))
            (.app (.bvar 3) (.binop .plus (.bvar 2) (.lit (.int 1)))))))
        (.app Occil.uniformInt (.lit (.int b))))))
    (.app digit.fst (.bvar 0))))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem valid_digit {b : ℕ} (d : Fin b) :
    decide ((b : ℤ) ≤ d) = false := by
  exact decide_eq_false (by exact_mod_cast Nat.not_le.mpr d.isLt)

private theorem twp_read (E : CoPset) (b : ℕ) (hb : 1 < b)
    (d : ℕ → Fin b) (digit : Val rT)
    (hdigit : ∀ k : ℕ, ⊢ tglWp E pl(&digit.fst #int ((k + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (d k : ℤ)⌝)))
    (F : Bool → ℝ≥0∞) (k : ℕ) :
    ⊢ ↯ (RealCoin.credit (bias d k) F) -∗
      tglWp E pl(&(read b digit) #int ((k + 1 : ℕ) : ℤ))
        (fun v : Val rT => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert %k Hcredit
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ %k Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  twp_pures
  simp only [UniformInt.uniformInt_openRec]
  twp_bind pl(&digit.fst #int ((k + 1 : ℕ) : ℤ))
  iapply tglWp_wand
  isplitl []
  · iapply hdigit k
  iintro %v %hv
  subst v
  twp_pures
  rw [valid_digit, Bool.or_false]
  twp_pure
  simp only [UniformInt.uniformInt_openRec]
  twp_bind pl(&Occil.uniformInt #int (b : ℤ))
  icombine Hcredit Hterm as Htotal
  ihave Hsample := ErrorCredit.weaken (expectation hb d k F ε) $$ Htotal
  iapply tglWp_wand
  isplitl [Hsample]
  · iapply (UniformInt.twp_uniformInt E b (by omega) (rankCredit d k F ε)) $$ Hsample
  iintro %v ⟨%j, %hv, %hj, Hcredit⟩
  subst v
  twp_pures
  by_cases hlt : j < d k
  · rw [show decide ((j : ℤ) < (d k : ℤ)) = true by exact_mod_cast decide_eq_true hlt]
    twp_pures
    twp_value
    imodintro
    iexists true
    isimp only [rankCredit, ite_eq_left hlt] at Hcredit
    iframe Hcredit
    itrivial
  · rw [show decide ((j : ℤ) < (d k : ℤ)) = false by exact_mod_cast decide_eq_false hlt]
    twp_pures
    by_cases hgt : (d k).val < j
    · rw [show decide ((d k : ℤ) < (j : ℤ)) = true by exact_mod_cast decide_eq_true hgt]
      twp_pures
      twp_value
      imodintro
      iexists false
      isimp only [rankCredit, ite_eq_right hlt, ite_eq_left hgt] at Hcredit
      iframe Hcredit
      itrivial
    · rw [show decide ((d k : ℤ) < (j : ℤ)) = false by exact_mod_cast decide_eq_false hgt]
      twp_pure
      isimp only [rankCredit, ite_eq_right hlt, ite_eq_right hgt] at Hcredit
      ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
      twp_pure
      simp only [UniformInt.uniformInt_openRec]
      isimp [read, Exp.openRec, ProbLang.openRec_val_fst,
        UniformInt.uniformInt_openRec] at IH
      iapply IH $$ Hterm Hcredit

/-- The digit algorithm samples the real represented by the supplied expansion. -/
theorem twp_fromDigits (E : CoPset) (b : ℕ) (hb : 1 < b)
    (d : ℕ → Fin b) (digit : Val rT)
    (hdigit : ∀ k : ℕ, ⊢ tglWp E pl(&digit.fst #int ((k + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (d k : ℤ)⌝)))
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias d 0) F) -∗
      tglWp E pl(&Occil.Constants.fromDigits #int (b : ℤ) &digit.fst #())
        (fun v : Val rT => iprop(∃ a : Bool, ⌜v = Val.bool a⌝ ∗ ↯ (F a))) := by
  have hread := twp_read (rT := rT) (GF := GF) E b hb d digit hdigit F 0
  simp [read] at hread
  iintro Hcredit
  twp_pures
  rw [show decide ((b : ℤ) < 2) = false by exact decide_eq_false (by omega)]
  iterate 2 twp_pure
  simp only [UniformInt.uniformInt_closeRec, UniformInt.uniformInt_openRec]
  iapply hread $$ Hcredit

/-- Typed Bernoulli specification, including both endpoint digit expansions. -/
theorem fromDigits_distSpec (E : CoPset) (b : ℕ) (hb : 1 < b)
    (d : ℕ → Fin b) (digit : Val rT)
    (hdigit : ∀ k : ℕ, ⊢ tglWp E pl(&digit.fst #int ((k + 1 : ℕ) : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.int (d k : ℤ)⌝))) :
    IsDistSpec (GF := GF) E
      pl(&Occil.Constants.fromDigits #int (b : ℤ) &digit.fst #())
      (RealCoin.law (bias d 0)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_fromDigits E b hb d digit hdigit F)

end specification

end

end SampLib.FromDigits
