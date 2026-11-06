import SampLib.Weighted.Syntax.Optimal
import SampLib.Weighted.Laws.OptimalEncoding

/-! # Deterministic row preprocessing for the optimal loaded-dice sampler -/

open ProbLang

namespace SampLib.Optimal

abbrev listValNatInts {rT : Type} [ProbLangℝ rT] (ws : List ℕ) : Val rT :=
  listVal (fun n : ℕ => Val.int (n : ℤ)) ws

private def scalar {rT : Type} (k l m : ℕ) : Exp rT := pl%
  if #int (m : ℤ) = #int (OptimalEncoding.denominator k l : ℤ) then
    #int ((2 ^ k : ℕ) : ℤ) - #1 else
  if #int (l : ℤ) = #int (k : ℤ) then #int (m : ℤ) else
  if #int (l : ℤ) = #0 then #int (m : ℤ) else
    (#int (m : ℤ) / (#int ((2 ^ (k - l) : ℕ) : ℤ) - #1)) *
        #int ((2 ^ (k - l) : ℕ) : ℤ) +
      #int (m : ℤ) % (#int ((2 ^ (k - l) : ℕ) : ℤ) - #1)

private theorem block_cast (k l m : ℕ) :
    ((m / (2 ^ (k - l) - 1) * 2 ^ (k - l) + m % (2 ^ (k - l) - 1) : ℕ) : ℤ) =
      (m : ℤ) / (((2 ^ (k - l) : ℕ) : ℤ) - 1) * ((2 ^ (k - l) : ℕ) : ℤ) +
        (m : ℤ) % (((2 ^ (k - l) : ℕ) : ℤ) - 1) := by
  rw [Int.natCast_add, Int.natCast_mul, Int.natCast_div, Int.natCast_mod,
    Int.natCast_sub (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)), Int.natCast_one]

private theorem power_cast (k : ℕ) : (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) := by norm_cast

private theorem equality_test {rT : Type} [BEq rT] (a b : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int (b : ℤ)) = decide (a = b) := by
  change decide ((a : ℤ) = (b : ℤ)) = decide (a = b)
  simp only [Int.natCast_inj]

private theorem zero_test {rT : Type} [BEq rT] (a : ℕ) :
    ((BaseLit.int (a : ℤ) : BaseLit rT) == .int 0) = decide (a = 0) := by
  change decide ((a : ℤ) = 0) = decide (a = 0)
  simp only [Int.natCast_eq_zero]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The artificial rejection row is appended without changing any original row. -/
theorem twp_append (E : CoPset) (r : ℕ) (ws : List ℕ) :
    ⊢ tglWp E pl(&(Program.append r) &(listValNatInts ws).fst)
      (fun v : Val rT => iprop(⌜v = listValNatInts (ws ++ [r])⌝)) := by
  induction ws with
  | nil =>
    simp only [listValNatInts, listVal, List.nil_append]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    simp only [listValNatInts, listVal, List.cons_append]
    iterate 5 twp_pure
    twp_bind pl(&(Program.append r) &(listValNatInts ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    simp only [Exp.ofVal]
    twp_pures
    change ⊢ tglWp E (Exp.ofVal (listValNatInts (rT := rT) (w :: (ws ++ [r])))) _
    iapply tglWp_value
    ipureintro
    rfl

private theorem twp_scalar (E : CoPset) (k l m : ℕ) (hl : l < k) :
    ⊢ tglWp E (scalar k l m)
      (fun v : Val rT => iprop(⌜v = Val.int (OptimalEncoding.binary k l m : ℤ)⌝)) := by
  unfold scalar
  twp_pure
  rw [equality_test]
  by_cases hm : m = OptimalEncoding.denominator k l
  · rw [decide_eq_true hm]
    twp_pures
    twp_value
    imodintro
    ipureintro
    apply Val.ext
    simp [OptimalEncoding.binary, hm, Int.natCast_sub (one_le_pow₀ (by decide : (1 : ℕ) ≤ 2))]
  · rw [decide_eq_false hm]
    twp_pure
    twp_pure
    rw [equality_test, decide_eq_false (Nat.ne_of_lt hl)]
    twp_pure
    twp_pure
    rw [zero_test]
    by_cases hzero : l = 0
    · rw [decide_eq_true hzero]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp only [OptimalEncoding.binary, ite_eq_right hm,
        ite_eq_right (Nat.ne_of_lt hl), ite_eq_left hzero]
    · rw [decide_eq_false hzero]
      twp_pures
      twp_value
      imodintro
      ipureintro
      apply Val.ext
      simp only [OptimalEncoding.binary, ite_eq_right hm,
        ite_eq_right (Nat.ne_of_lt hl), ite_eq_right hzero]
      rw [block_cast]

/-- The source's converter implements the complete integer encoding, including endpoints. -/
theorem twp_encode (E : CoPset) (k l : ℕ) (hl : l < k) (ws : List ℕ) :
    ⊢ tglWp E pl(&(Program.encode k l (OptimalEncoding.denominator k l))
        &(listValNatInts ws).fst)
      (fun v : Val rT => iprop(⌜v = listValNatInts (ws.map (OptimalEncoding.binary k l))⌝)) := by
  induction ws with
  | nil =>
    simp only [listValNatInts, listVal, List.map_nil]
    twp_pures
    twp_value
    imodintro
    itrivial
  | cons w ws IH =>
    simp only [listValNatInts, listVal, List.map_cons]
    iterate 7 twp_pure
    rw [← Int.natCast_sub hl.le]
    twp_bind pl(&Occil.Weighted.integerPower #2 #int ((k - l : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply WeightedIntegerPower.twp_integerPower E 2 (k - l)
    iintro %v %hv
    subst v
    rw [power_cast]
    twp_pure
    twp_bind (scalar k l w)
    iapply tglWp_wand
    isplitl []
    · iapply twp_scalar E k l w hl
    iintro %v %hv
    subst v
    iterate 2 twp_pure
    twp_bind pl(&(Program.encode k l (OptimalEncoding.denominator k l))
      &(listValNatInts ws).fst)
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v %hv
    subst v
    simp only [Exp.ofVal]
    change ⊢ tglWp E (Exp.ofVal (listValNatInts (rT := rT)
      (OptimalEncoding.binary k l w :: ws.map (OptimalEncoding.binary k l)))) _
    iapply tglWp_value
    ipureintro
    rfl

end specification

end SampLib.Optimal
