import SampLib.Distributions.AlternatingPermutationKernel
import SampLib.Syntax.ClosedExp

/-! # Finite alternating comparisons

The number of comparisons decreases at every recursive call. The CTE proof uses
the Volterra success mass as its continuation credit, with no termination slack.
-/

open ProbLang
open LawfulProbLangℝ (unifUnit)
open scoped ENNReal

namespace SampLib.AlternatingPermutationPath

noncomputable section

open AlternatingPermutationKernel

def up (i : ℕ) : Bool := decide (i % 2 = 1)

def loopSource (count : ℤ) : Exp ℝ := pl%
  rec draw i last :=
    if #int (count : ℤ) <= i then #true else
      let next := urand;
      if i % #2 = #1 then
        if next < last then #false else draw (i + #1) next
      else if last < next then #false else draw (i + #1) next

def loop (count : ℕ) : Exp ℝ := loopSource count

/-- Closed de Bruijn form, shared with the enclosing sampler's recursive value. -/
def loopCode (count : ℤ) : Exp ℝ :=
  let retry := .app (.app (.bvar 3) (.binop .plus (.bvar 2) (.lit (.int 1)))) (.bvar 0)
  let branch := .cond (.binop .eq (.binop .mod (.bvar 2) (.lit (.int 2))) (.lit (.int 1)))
    (.cond (.binop .lt (.bvar 0) (.bvar 1)) (.lit (.bool false)) retry)
    (.cond (.binop .lt (.bvar 1) (.bvar 0)) (.lit (.bool false)) retry)
  .fix (.lam (.lam (.cond (.binop .le (.lit (.int count)) (.bvar 1)) (.lit (.bool true))
    (.app (.lam branch) (.sample unifRealName (.lit .unit) (.lit .unit))))))

instance loopCode_closed (count : ℤ) : ClosedExp (loopCode count) where
  lc := by unfold loopCode; is_lc
  fv := by simp [loopCode, Exp.fv]

theorem loopSource_eq_code (count : ℤ) : loopSource count = loopCode count := by
  simp [loopSource, loopCode, Exp.close, Exp.closeRec, Var.internal.injEq]

theorem loop_eq_code (count : ℕ) : loop count = loopCode (count : ℤ) :=
  loopSource_eq_code count

@[simp] theorem up_one : up 1 = true := rfl

private theorem up_succ (i : ℕ) : up (i + 1) = !(up i) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have h' : (i + 1) % 2 = 1 := by omega
    simp [up, h, h']
  · have h' : (i + 1) % 2 = 0 := by omega
    simp [up, h, h']

private theorem int_beq (a b : ℤ) :
    ((BaseLit.int a : BaseLit ℝ) == .int b) = (a == b) := rfl

private theorem parity_test (i : ℕ) : ((i : ℤ) % 2 == 1) = up i := by
  by_cases h : i % 2 = 1
  · have ht : ((i : ℤ) % 2 == 1) = true := beq_iff_eq.mpr (by omega)
    simp [up, h, ht]
  · have hf : ((i : ℤ) % 2 == 1) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp [up, h, hf]

private theorem continuing (i n : ℕ) : decide (((i + (n + 1) : ℕ) : ℤ) ≤ i) = false :=
  decide_eq_false (by omega)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

/-- The continuation probability is the mass of the remaining finite path. -/
theorem twp_loop (E : CoPset) (n i : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (pathBias n (up i) x) F) -∗
      tglWp E pl(&(loop (i + n)) #int (i : ℤ) #real x)
        (fun v : Val ℝ => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  induction n generalizing i x with
  | zero =>
    iintro Hcredit
    twp_pures
    simp only [Nat.add_zero, le_refl, decide_true]
    twp_pure
    twp_value
    imodintro
    iexists true
    isimp only [pathBias_zero, RealCoin.credit_one] at Hcredit
    iframe Hcredit
    itrivial
  | succ n IH =>
    iintro Hcredit
    iterate 4 twp_pure
    rw [continuing i n]
    twp_pure
    twp_bind pl(urand)
    isimp only [← expectation n (up i) x hx F] at Hcredit
    iapply (twp_urand_exp (ε₂ := kernel n (up i) x F)
      (measurable_kernel n (up i) x F) le_rfl) $$ Hcredit
    iintro %y ⟨%hy, Hcredit⟩
    have hy' := mem_unifUnitSupport_real.mp hy
    have hyI : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy'.1.le, hy'.2.le⟩
    iterate 3 twp_pure
    rw [int_beq, parity_test i]
    cases hi : up i
    · twp_pure
      twp_pure
      rcases hxy : ProbLangℝ.realLt x y with _ | _
      · have hle : y ≤ x := le_of_not_gt (of_decide_eq_false hxy)
        isimp only [kernel, nextBias, hi, Bool.false_eq_true, ite_false, hle, ite_true]
          at Hcredit
        twp_pure
        twp_pure
        rw [show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by omega]
        have hnext := IH (i + 1) y hyI
        rw [show i + 1 + n = i + (n + 1) by omega, up_succ, hi, Bool.not_false]
          at hnext
        simp only [loop_eq_code, Nat.cast_add, Nat.cast_one] at hnext
        isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_one]
        ieval (change _ ⊢ tglWp E (Exp.app
          (Exp.app (loopSource ((i : ℤ) + ((n : ℤ) + 1))) (.lit (.int ((i : ℤ) + 1))))
          (.lit (.real y))) _)
        rw [loopSource_eq_code]
        iapply hnext $$ Hcredit
      · have hlt := of_decide_eq_true hxy
        isimp only [kernel, nextBias, hi, Bool.false_eq_true, ite_false,
          not_le.mpr hlt, ite_true, RealCoin.credit_zero]
          at Hcredit
        twp_pures
        twp_value
        imodintro
        iexists false
        iframe Hcredit
        itrivial
    · twp_pure
      twp_pure
      rcases hyx : ProbLangℝ.realLt y x with _ | _
      · have hle : x ≤ y := le_of_not_gt (of_decide_eq_false hyx)
        isimp only [kernel, nextBias, hi, ite_true, hle] at Hcredit
        twp_pure
        twp_pure
        rw [show (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by omega]
        have hnext := IH (i + 1) y hyI
        rw [show i + 1 + n = i + (n + 1) by omega, up_succ, hi, Bool.not_true]
          at hnext
        simp only [loop_eq_code, Nat.cast_add, Nat.cast_one] at hnext
        isimp only [Exp.ofVal, Nat.cast_add, Nat.cast_one]
        ieval (change _ ⊢ tglWp E (Exp.app
          (Exp.app (loopSource ((i : ℤ) + ((n : ℤ) + 1))) (.lit (.int ((i : ℤ) + 1))))
          (.lit (.real y))) _)
        rw [loopSource_eq_code]
        iapply hnext $$ Hcredit
      · have hlt := of_decide_eq_true hyx
        isimp only [kernel, nextBias, hi, ite_true, not_le.mpr hlt, ite_false,
          RealCoin.credit_zero] at Hcredit
        twp_pures
        twp_value
        imodintro
        iexists false
        iframe Hcredit
        itrivial

end specification

end

end SampLib.AlternatingPermutationPath
