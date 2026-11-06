import SampLib.LatentPiCoordinate
import SampLib.Distributions.FiniteProductCons
import SampLib.GeneralSyntax

/-! # Repeated independent construction of one deferred component law -/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.PiModel

noncomputable section

/-- Recursive initial states follow the same list order as the source constructor. -/
def initial {S : Type} (s : S) : (n : ℕ) → Fin n → S
  | 0 => Fin.elim0
  | n + 1 => Fin.cons s (initial s n)

theorem initial_eq_const {S : Type} (s : S) (n : ℕ) : initial s n = fun _ => s := by
  induction n with
  | zero => exact funext (fun i => i.elim0)
  | succ n ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun ih j

section mathematics

open MeasureTheory

variable {Ω S : Type} [MeasurableSpace Ω]

def headCredit {n : ℕ} (D : Model Ω S) (s : Fin n → S)
    (F : (Fin (n + 1) → Ω) → ℝ≥0∞) (x : Ω) : ℝ≥0∞ :=
  ∫⁻ tail, F (Fin.cons x tail) ∂(world (fun _ => D)).posterior s

def tailCredit {n : ℕ} (D : Model Ω S) (s : S)
    (F : (Fin (n + 1) → Ω) → ℝ≥0∞) (tail : Fin n → Ω) : ℝ≥0∞ :=
  ∫⁻ x, F (Fin.cons x tail) ∂D.posterior s

theorem measurable_headCredit {n : ℕ} (D : Model Ω S) (s : Fin n → S)
    {F : (Fin (n + 1) → Ω) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (headCredit D s F) :=
  (hF.comp FiniteProductPosterior.measurable_cons).lintegral_prod_right'

theorem measurable_tailCredit {n : ℕ} (D : Model Ω S) (s : S)
    {F : (Fin (n + 1) → Ω) → ℝ≥0∞} (hF : Measurable F) :
    Measurable (tailCredit D s F) :=
  (hF.comp FiniteProductPosterior.measurable_cons).lintegral_prod_left'

theorem expectation_head {n : ℕ} (D : Model Ω S) (s : S) (tail : Fin n → S)
    (F : (Fin (n + 1) → Ω) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(world (fun _ => D)).posterior (Fin.cons s tail) =
      ∫⁻ x, headCredit D tail F x ∂D.posterior s := by
  simpa only [world, posterior, headCredit, Fin.cons_zero, Fin.cons_succ] using
    FiniteProductPosterior.expectation_cons
      (fun i : Fin (n + 1) => D.posterior ((Fin.cons s tail : Fin (n + 1) → S) i)) F hF

theorem expectation_tail {n : ℕ} (D : Model Ω S) (s : S) (tail : Fin n → S)
    (F : (Fin (n + 1) → Ω) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(world (fun _ => D)).posterior (Fin.cons s tail) =
      ∫⁻ x, tailCredit D s F x ∂(world (fun _ => D)).posterior tail := by
  simpa only [world, posterior, tailCredit, Fin.cons_zero, Fin.cons_succ] using
    FiniteProductPosterior.expectation_cons_right
      (fun i : Fin (n + 1) => D.posterior ((Fin.cons s tail : Fin (n + 1) → S) i)) F hF

private theorem refines_cons {n : ℕ} (D : Model Ω S) {s t : S} (hst : D.refines s t)
    {p q : Fin n → S} (hpq : (world (fun _ => D)).refines p q) :
    (world (fun _ => D)).refines (Fin.cons s p) (Fin.cons t q) := by
  intro i
  refine Fin.cases hst (fun j => hpq j) i

end mathematics

private theorem encode_cons {rT : Type} [ProbLangℝ rT] {n : ℕ} (head : Val rT)
    (tail : Fin n → Val rT) :
    pl(inr((&head.fst, &(vectorVal tail).fst))) = Exp.ofVal (vectorVal (Fin.cons head tail)) := by
  simp [Exp.ofVal, vectorVal, List.ofFn_succ, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- Each actual constructor call receives its conditional joint credit. -/
theorem repeatSample_payloadSpec (E : CoPset) (D : Model Ω S) (s : S)
    (O : Val rT → S → IProp GF) (sample : Val rT)
    (h : IsLatentPayloadSpec E pl(&sample.fst #()) D s O) (n : ℕ) :
    IsLatentPayloadSpec E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
      (world (fun _ : Fin n => D)) (initial s n)
      (VectorOwns (owns (fun _ => S) (fun _ => O))) := by
  induction n with
  | zero =>
    refine ⟨fun F _ => ?_⟩
    iintro Hcredit
    twp_pures
    twp_value
    imodintro
    iexists initial s 0
    isplitl []
    · ipureintro
      exact fun i => i.elim0
    isplitl []
    · isimp only [VectorOwns, owns]
      iexists Fin.elim0
      ipureintro
      exact ⟨rfl, trivial⟩
    iexact Hcredit
  | succ n ih =>
    refine ⟨fun F hF => ?_⟩
    iintro Hcredit
    twp_pures
    twp_bind pl(&sample.fst #())
    isimp only [initial, expectation_head D s (initial s n) F hF] at Hcredit
    iapply (h.wp (headCredit D (initial s n) F) (measurable_headCredit D _ hF) _) $$ Hcredit
    iintro %head %t %ht Hhead Hcredit
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
    isimp only [← expectation_head D t (initial s n) F hF,
      expectation_tail D t (initial s n) F hF] at Hcredit
    iapply (ih.wp (tailCredit D t F) (measurable_tailCredit D t hF) _) $$ Hcredit
    iintro %v %q %hq Htail Hcredit
    isimp only [VectorOwns] at Htail
    icases Htail with ⟨%tail, %hv, Htail⟩
    subst v
    simp only [Exp.ofVal]
    rw [encode_cons]
    iapply (tglWp_value (v := vectorVal (Fin.cons head tail)))
    isimp only [← expectation_tail D t q F hF] at Hcredit
    iexists Fin.cons t q
    isplitl []
    · ipureintro
      exact refines_cons D ht hq
    isplitl [Hhead Htail]
    · isimp only [VectorOwns]
      iexists Fin.cons head tail
      isplitl []
      · ipureintro
        rfl
      isimp only [owns, Fin.cons_zero, Fin.tail_cons]
      iframe Hhead Htail
    iexact Hcredit

/-- The actual repeated constructor provides every coordinate's strong observation protocol. -/
theorem repeatSample_vectorSpec (E : CoPset) (D : Model Ω S) (R : Representation D) (s : S)
    (O : Val rT → S → IProp GF) (sample : Val rT)
    (h : IsRepresentedDistSpec E pl(&sample.fst #()) D R s O) (n : ℕ) :
    IsRepresentedVectorSpec E pl(&Occil.repeatSample &sample.fst #int (n : ℤ))
      (world (fun _ : Fin n => D)) (fun i => view (fun _ => D) i)
      (fun i => representation (fun _ => D) (fun _ => R) i) (initial s n)
      (owns (fun _ => S) (fun _ => O)) where
  sameWorld i := sameWorld _ i
  payload := repeatSample_payloadSpec E D s O sample h.toIsLatentPayloadSpec n
  coordinate handles i := represented_coordinateSpec E _ _ _ handles i h.oracle

end specification

end

end SampLib.LatentReal.PiModel
