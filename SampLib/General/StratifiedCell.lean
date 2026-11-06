import SampLib.General.Stratified1D
import SampLib.General.Support.GeneralIntegerPower

/-! # Independent jitter inside a Cartesian grid cell

Successive base-`bins` digits of the cell label select the coordinate strata.
-/

open ProbLang
open SampLib.RndIntExcRange (rndIntExcRange_openRec rndIntExcRange_closeRec)
open scoped ENNReal

namespace SampLib.StratifiedCell

noncomputable section

section mathematics

open MeasureTheory

/-- Uniform coordinates in the strata selected by the cell's base digits. -/
def law (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) :
    ℕ → ℕ → Measure (List ℤ)
  | 0, _ => Measure.dirac []
  | n + 1, cell => ((law scale bins hb h n (cell / bins)).prod
      (Stratified1D.coordinate scale bins hb h (cell % bins))).map (fun z => z.2 :: z.1)

instance (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale) (n cell : ℕ) :
    IsProbabilityMeasure (law scale bins hb h n cell) := by
  induction n generalizing cell with
  | zero => dsimp [law]; infer_instance
  | succ n IH =>
    let := IH (cell / bins)
    constructor
    rw [law, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- Independence separates a coordinate's stratum from the remaining digits. -/
theorem expectation (scale bins : ℕ) (hb : 0 < bins) (h : bins ≤ scale)
    (n cell : ℕ) (F : List ℤ → ℝ≥0∞) :
    ∫⁻ ys, ∫⁻ x, F (x :: ys) ∂Stratified1D.coordinate scale bins hb h (cell % bins)
        ∂law scale bins hb h n (cell / bins) =
      ∫⁻ ys, F ys ∂law scale bins hb h (n + 1) cell := by
  rw [law, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end mathematics

private def build {rT : Type _} (scale bins : ℕ) : Exp rT := pl%
  rec coordinate remaining index := if remaining = #0 then inl(#()) else
    let digit := index % #int (bins : ℤ);
    let lower := digit * #int (scale : ℤ) / #int (bins : ℤ);
    let upper := (digit + #1) * #int (scale : ℤ) / #int (bins : ℤ);
    inr((&Occil.rndIntExcRange lower upper,
      coordinate (remaining - #1) (index / #int (bins : ℤ))))

private theorem pred_cast (n : ℕ) : ((n + 1 : ℕ) : ℤ) - 1 = n := by omega

private theorem lower_eq (scale bins cell : ℕ) :
    (cell : ℤ) % bins * scale / bins = Stratified1D.boundary scale bins (cell % bins) := by
  simp [Stratified1D.boundary, Int.natCast_ediv]

private theorem upper_eq (scale bins cell : ℕ) :
    ((cell : ℤ) % bins + 1) * scale / bins =
      Stratified1D.boundary scale bins (cell % bins + 1) := by
  simp [Stratified1D.boundary, Int.natCast_ediv, Nat.cast_add]

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (x : ℤ) (xs : List ℤ) :
    pl(inr(({Exp.ofVal (Val.int x)}, {Exp.ofVal (listVal Val.int xs)}))) =
      Exp.ofVal (listVal Val.int (x :: xs) : Val rT) := by simp [Exp.ofVal, listVal]

private theorem valid_test (scale bins dimension : ℕ) (hb : 0 < bins)
    (h : bins ≤ scale) (hd : 0 < dimension) :
    Bool.or (Bool.or (decide ((bins : ℤ) ≤ 0))
      (decide ((scale : ℤ) < bins))) (decide ((dimension : ℤ) ≤ 0)) = false := by
  simp [Nat.ne_of_gt hb, Nat.ne_of_gt hd, not_lt.mpr (Int.ofNat_le.mpr h)]

private theorem cell_test (bins dimension cell : ℕ) (hc : cell < bins ^ dimension) :
    decide ((cell : ℤ) < (bins : ℤ) ^ dimension) = true :=
  decide_eq_true (by exact_mod_cast hc)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_build (E : CoPset) (scale bins : ℕ) (hb : 0 < bins)
    (h : bins ≤ scale) (n cell : ℕ) (F : List ℤ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law scale bins hb h n cell) -∗
      tglWp E pl(&(build (rT := rT) scale bins) #int (n : ℤ) #int (cell : ℤ))
        (fun v : Val rT => iprop(∃ ys : List ℤ, ⌜v = listVal Val.int ys⌝ ∗ ↯ (F ys))) := by
  induction n generalizing cell F with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | succ n IH =>
    iintro Hcredit
    iterate 16 twp_pure
    simp only [rndIntExcRange_openRec, rndIntExcRange_closeRec]
    rw [pred_cast, ← Int.natCast_ediv]
    twp_bind pl(&(build (rT := rT) scale bins) #int (n : ℤ) #int ((cell / bins : ℕ) : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · isimp only [← expectation scale bins hb h n cell F] at Hcredit
      iapply (IH (cell / bins)
        (fun ys => ∫⁻ x, F (x :: ys) ∂Stratified1D.coordinate scale bins hb h (cell % bins)))
        $$ Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    rw [lower_eq, upper_eq]
    twp_bind pl(&Occil.rndIntExcRange
      #int (Stratified1D.boundary scale bins (cell % bins) : ℤ)
      #int (Stratified1D.boundary scale bins (cell % bins + 1) : ℤ))
    isimp only [Stratified1D.coordinate] at Hcredit
    iapply ((RndIntExcRange.rndIntExcRange_distSpec E _ _
      (Int.ofNat_lt.mpr (Stratified1D.boundary_lt scale bins (cell % bins) hb h))).wp
      (fun x => F (x :: ys)) (measurable_of_countable _) _) $$ Hcredit
    iintro %x Hcredit
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.int (x :: ys)))
    iexists x :: ys
    iframe Hcredit
    itrivial

/-- A point in any valid Cartesian cell, with independent coordinate jitter. -/
theorem stratifiedCell_distSpec (E : CoPset) (scale bins dimension cell : ℕ)
    (hb : 0 < bins) (h : bins ≤ scale) (hd : 0 < dimension) (hc : cell < bins ^ dimension) :
    IsDistSpec (GF := GF) E
      pl(&Occil.General.stratifiedCell #int (scale : ℤ) #int (bins : ℤ)
        #int (dimension : ℤ) #int (cell : ℤ))
      (law scale bins hb h dimension cell) (listVal Val.int) where
  spec F _ := by
    have hbuild := twp_build (rT := rT) (GF := GF) E scale bins hb h dimension cell F
    simp [build, Exp.close, Exp.closeRec] at hbuild
    iintro Hcredit
    twp_pures
    simp only [Bool.or_false]
    rw [valid_test scale bins dimension hb h hd]
    twp_pure
    twp_pure
    simp only [GeneralIntegerPower.integerPower_closeRec,
      GeneralIntegerPower.integerPower_openRec, rndIntExcRange_openRec, rndIntExcRange_closeRec]
    twp_bind pl(&Occil.General.integerPower #int (bins : ℤ) #int (dimension : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply GeneralIntegerPower.twp_integerPower E (bins : ℤ) dimension
    iintro %v %hv
    subst v
    twp_pures
    rw [cell_test bins dimension cell hc]
    twp_pure
    iapply hbuild
    iexact Hcredit

end specification

end

end SampLib.StratifiedCell
