import SampLib.Combinatorial.Choice
import Metrology.Iris.LocalBI

/-!
# Sampling a list with replacement

The output law is the independent product of uniform positions, encoded as list
entries. Distinct positions with equal entries keep their multiplicities.
-/

open Set ProbLang
open scoped ENNReal

namespace SampLib.SampleWithReplacement

noncomputable section

section distribution

open MeasureTheory Measure

variable {α : Type _} [MeasurableSpace α]

private theorem measurable_cons (n : ℕ) :
    Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n + 1) → α)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
      (measurable_snd : Measurable (Prod.snd : α × (Fin n → α) → (Fin n → α)))

/-- Independent draws from `μ`, in the order returned by the algorithm. -/
def law (μ : Measure α) : (n : ℕ) → Measure (Fin n → α)
  | 0 => dirac (Fin.elim0)
  | n + 1 => (μ.prod (law μ n)).map (fun z => Fin.cons z.1 z.2)

instance law_zero_prob (μ : Measure α) : IsProbabilityMeasure (law μ 0) := by
  dsimp [law]
  infer_instance

instance (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (law μ n) := by
  induction n with
  | zero => infer_instance
  | succ n IH =>
    let _ := IH
    constructor
    rw [law, Measure.map_apply (measurable_cons n) MeasurableSet.univ]
    simp

/-- Fubini expresses the independent draw as its two continuation expectations. -/
theorem lintegral_law_succ (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin (n + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ys, F ys ∂law μ (n + 1) =
      ∫⁻ x, ∫⁻ ys, F (Fin.cons x ys) ∂law μ n ∂μ := by
  rw [law, lintegral_map hF (measurable_cons n)]
  exact lintegral_prod _ (hF.comp (measurable_cons n)).aemeasurable

private theorem measurable_tail (n : ℕ) (x : α)
    (F : (Fin (n + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun ys => F (Fin.cons x ys)) := by
  simpa only [Function.comp_def] using
    (hF.comp (measurable_cons n)).comp measurable_prodMk_left

private theorem measurable_cont (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin (n + 1) → α) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun x => ∫⁻ ys, F (Fin.cons x ys) ∂law μ n) := by
  apply Measurable.lintegral_prod_right
  simpa only [Function.comp_def, Function.uncurry_def] using hF.comp (measurable_cons n)

end distribution

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) {n : ℕ} (x : α) (ys : Fin n → α) :
    pl(inr(({(encode x).fst}, {Exp.ofVal (listVal encode (List.ofFn ys))}))) =
      Exp.ofVal (listVal encode (List.ofFn (Fin.cons x ys))) := by
  simp [Exp.ofVal, List.ofFn_succ, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {α : Type _} [MeasurableSpace α]
local bi (IProp GF)

private theorem twp_repeatSample_zero (E : CoPset) (sample : Val rT) :
    ⊢ tglWp E pl(&Occil.repeatSample &sample.fst #int (0 : ℤ))
      (fun v : Val rT => iprop(⌜v = Val.inl Val.unit⌝)) := by
  twp_pures
  twp_value
  imodintro
  itrivial

/-- Repeated callback calls yield the independent product law. -/
theorem twp_repeatSample (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (encode : α → Val rT) (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ encode) (n : ℕ)
    (F : (Fin n → α) → ℝ≥0∞) (hF : Measurable F) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law μ n) -∗
      tglWp E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
        (fun v : Val rT => iprop(∃ ys : Fin n → α,
          ⌜v = listVal encode (List.ofFn ys)⌝ ∗ ↯ (F ys))) := by
  induction n with
  | zero =>
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists Fin.elim0
    isimp only [law, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    simp [List.ofFn_zero, listVal]
  | succ n IH =>
    iintro Hcredit
    twp_pures
    twp_bind pl(&sample.fst #())
    isimp only [lintegral_law_succ μ n F hF] at Hcredit
    iapply (hsample.wp
      (fun x => ∫⁻ ys, F (Fin.cons x ys) ∂law μ n)
      (measurable_cont μ n F hF) _) $$ Hcredit
    iintro %x Hcredit
    twp_pure
    twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply (IH (fun ys => F (Fin.cons x ys))
        (measurable_tail n x F hF))
      iexact Hcredit
    iintro %v ⟨%ys, %hv, Hcredit⟩
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal encode (List.ofFn (Fin.cons x ys))))
    iexists Fin.cons x ys
    iframe Hcredit
    itrivial

/-- Reusable independent repetition specification. -/
theorem repeatSample_distSpec (E : CoPset) (μ : MeasureTheory.Measure α)
    [MeasureTheory.IsProbabilityMeasure μ] (encode : α → Val rT) (sample : Val rT)
    (hsample : IsDistSpec (GF := GF) E pl(&sample.fst #()) μ encode) (n : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
      (law μ n) (fun ys => listVal encode (List.ofFn ys)) where
  spec F hF := wand_entails (twp_repeatSample E μ encode sample hsample n F hF)

end specification

section collection

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

private def chooser (encode : α → Val rT) (xs : List α) : Val rT :=
  ⟨.lam (.app Occil.choice (listVal encode xs).fst), .lam (by is_lc), by is_lc⟩

private theorem chooser_spec (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] :
    IsDistSpec (GF := GF) E pl(&(chooser encode xs).fst #()) (Choice.law xs.length)
      (fun i => encode (xs.get i)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&Occil.choice &(listVal encode xs).fst)
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (Choice.choice_distSpec E encode xs).spec F hF $$ Hcredit

/-- Independent uniform positions, encoded to the original list entries. -/
theorem sampleWithReplacement_distSpec (E : CoPset) (encode : α → Val rT)
    (xs : List α) [NeZero xs.length] (n : ℕ) :
    IsDistSpec (GF := GF) E
      pl(&Occil.sampleWithReplacement &(listVal encode xs).fst #int (n : ℤ))
      (law (Choice.law xs.length) n)
      (fun ys => listVal (fun i => encode (xs.get i)) (List.ofFn ys)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_bind pl(&Occil.repeatSample &(chooser encode xs).fst #int (n : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (repeatSample_distSpec E (Choice.law xs.length)
      (fun i => encode (xs.get i)) (chooser encode xs) (chooser_spec E encode xs) n).spec
      F hF $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
/-- Zero draws return the empty list, including when the input list is empty. -/
theorem sampleWithReplacement_zero_distSpec (E : CoPset) (encode : α → Val rT)
    (xs : List α) :
    IsDistSpec (GF := GF) E
      pl(&Occil.sampleWithReplacement &(listVal encode xs).fst #int (0 : ℤ))
      (MeasureTheory.Measure.dirac ()) (fun _ : Unit => listVal encode []) where
  spec F _ := by
    iintro Hcredit
    twp_pure
    twp_pure
    twp_pure
    twp_pure
    twp_bind pl(&Occil.repeatSample &(chooser encode xs).fst #int (0 : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply (twp_repeatSample_zero E (chooser encode xs))
    iintro %v %hv
    subst v
    iapply (tglWp_value (v := Val.inl Val.unit))
    iexists ()
    isimp only [MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    rfl

end collection

end

end SampLib.SampleWithReplacement
