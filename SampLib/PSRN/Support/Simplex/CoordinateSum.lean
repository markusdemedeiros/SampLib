import SampLib.PSRN.Support.Arithmetic.ConstantView
import SampLib.PSRN.Support.Arithmetic.Relations
import SampLib.Latent.LatentVectorSpec
import SampLib.PSRN.Syntax.PSRNCoordinateSum
import SampLib.PSRN.Support.Represented.Addition

/-! # The common sum of a vector of shared latent views

The constructor and observer keep one latent world and never duplicate it. The sum
keeps each coordinate's deterministic representation.
-/

namespace SampLib.LatentReal.CoordinateSum

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

private def projection (D : Model Ω S) : (n : ℕ) → (views : Fin n → Model Ω S) →
    (∀ i, D.SameWorld (views i)) → {N : Model Ω S // D.SameWorld N}
  | 0, _, _ => ⟨D.constant 0, D.sameWorld_constant 0⟩
  | n + 1, views, hviews =>
    let tail := projection D n (Fin.tail views) (fun i => hviews i.succ)
    let hsum := (hviews 0).between tail.property
    ⟨(views 0).add tail.val hsum, (hviews 0).trans hsum.add_left⟩

/-- Adding coordinates retains the one posterior and physical refinement relation. -/
def model (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : Model Ω S := (projection D n views hviews).val

theorem sameWorld (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) : D.SameWorld (model D views hviews) :=
  (projection D n views hviews).property

/-- All terms refer to coordinates of the same latent sample. -/
theorem value_eq (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (x : Ω) :
    (model D views hviews).value x = ∑ i, (views i).value x := by
  induction n with
  | zero => simp [model, projection, Model.constant]
  | succ n ih =>
    simp only [model, projection, Model.add, Fin.sum_univ_succ]
    exact congrArg ((views 0).value x + ·)
      (by simpa only [model, Fin.tail] using ih (Fin.tail views) (fun i => hviews i.succ))

theorem measurableError (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (herror : ∀ i, (views i).MeasurableError) :
    (model D views hviews).MeasurableError := by
  induction n with
  | zero => exact fun _ => measurable_const
  | succ n ih =>
    exact (herror 0).add
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => herror i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ)))

end

end SampLib.LatentReal.CoordinateSum

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.CoordinateSum

open scoped SampLib.LatentReal.CoordinateSum

noncomputable section

def value {rT : Type} : {n : ℕ} → (Fin n → Val rT) → Val rT
  | 0, _ => LatentRational.value 0 1
  | _ + 1, handles => addVal (handles 0) (value (Fin.tail handles))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

theorem oracleSpec (E : CoPset) (D : Model Ω S) {n : ℕ}
    (views : Fin n → Model Ω S) (hviews : ∀ i, D.SameWorld (views i))
    (handles : Fin n → Val rT) (P : S → IProp GF)
    (hspec : ∀ i, IsViewSpec E (views i) P (handles i)) :
    IsViewSpec E (model D views hviews) P (value handles) := by
  induction n with
  | zero =>
    change IsViewSpec E (D.constant 0) P (LatentRational.value 0 1)
    simpa only [Int.cast_zero, Int.cast_one, zero_div] using
      constant_viewSpec E D P 0 1 (by decide)
  | succ n ih =>
    have htail := ih (Fin.tail views) (fun i => hviews i.succ)
      (Fin.tail handles) (fun i => hspec i.succ)
    exact add_oracleSpec E (views 0) (model D (Fin.tail views) (fun i => hviews i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ))) P
      (handles 0) (value (Fin.tail handles)) (hspec 0) htail

private theorem unfold_source (E : CoPset) (v : Val rT) (Φ : Val rT → IProp GF) :
    tglWp E (.app (openedValue (rT := rT)).fst v.fst) Φ ⊢
      tglWp E (.app (sourceValue (rT := rT)).fst v.fst) Φ := by
  have : PureExec (v.fst.isValue ∧ (sourceValue (rT := rT)).fst.IsLocallyClosed) 1
      (.app (sourceValue (rT := rT)).fst v.fst)
      (.app (Exp.open' sourceBody (sourceValue (rT := rT)).fst) v.fst) :=
    pureExec_app_fix (body := sourceBody (rT := rT)) (v := v.fst)
  rw [← opened_source]
  exact twp_pure_step_ctx [] _ ⟨⟨v.snd⟩, (sourceValue (rT := rT)).lc⟩

/-- The local sum captures the actual handles and performs no observations. -/
theorem twp_sum (E : CoPset) {n : ℕ} (handles : Fin n → Val rT)
    (P : S → IProp GF) (s : S) :
    P s ⊢ tglWp E pl(&source &(vectorVal handles).fst)
      (fun v => ViewOwns (value handles) P v s) := by
  induction n with
  | zero =>
    iintro Hstate
    simp only [vectorVal, List.ofFn_zero, listVal]
    rw [← source_fst]
    iapply unfold_source E (.inl .unit) _
    twp_pure
    simp only [openedBody, Exp.openRec, ProbLang.openRec_val_fst]
    twp_pure
    twp_pure
    simp only [ClosedExp.openRec]
    twp_pures
    twp_value
    imodintro
    isimp only [ViewOwns]
    iframe Hstate
    ipureintro
    rfl
  | succ n ih =>
    iintro Hstate
    rw [← source_fst]
    iapply unfold_source E (vectorVal handles) _
    twp_pure
    simp only [openedBody, Exp.openRec, ProbLang.openRec_val_fst,
      vectorVal, List.ofFn_succ, listVal]
    twp_pure
    twp_pure
    simp only [consBranchCode, Exp.openRec, ClosedExp.openRec]
    twp_pure
    twp_bind pl(&(sourceValue (rT := rT)).fst &(vectorVal (Fin.tail handles)).fst)
    iapply tglWp_wand
    isplitl [Hstate]
    · rw [source_fst]
      iapply ih (Fin.tail handles) $$ Hstate
    iintro %tail Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%htail, Hstate⟩
    subst tail
    twp_pure
    simp only [Exp.ofVal, value]
    simp only [id_eq]
    iapply twp_add E (handles 0) (value (Fin.tail handles)) P s $$ Hstate

end specification

end

end SampLib.LatentReal.CoordinateSum

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.CoordinateSum

noncomputable section

variable {Ω S : Type} [MeasurableSpace Ω]

/-- The represented denominator is the finite sum at the same requested precision. -/
def representation (D : Model Ω S) {n : ℕ} (views : Fin n → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (Rs : ∀ i, Representation (views i)) :
    Representation (model D views hviews) := by
  induction n with
  | zero => exact Representation.point D 0 0 1 (by decide) (by norm_num)
  | succ n ih =>
    exact Representation.add (views 0) (model D (Fin.tail views) (fun i => hviews i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ))) (Rs 0)
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => Rs i.succ))

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Repeated or aliased coordinates still consume one shared physical ownership. -/
theorem represented_oracleSpec (E : CoPset) (D : Model Ω S) {n : ℕ}
    (views : Fin n → Model Ω S) (hviews : ∀ i, D.SameWorld (views i))
    (Rs : ∀ i, Representation (views i)) (handles : Fin n → Val rT) (P : S → IProp GF)
    (hspec : ∀ i, IsRepresentedViewSpec E (views i) (Rs i) P (handles i)) :
    IsRepresentedViewSpec E (model D views hviews) (representation D views hviews Rs)
      P (value handles) := by
  induction n with
  | zero =>
    exact represented_point_viewSpec E D P 0 0 1 (by decide) (by norm_num)
  | succ n ih =>
    exact represented_add_oracleSpec E (views 0)
      (model D (Fin.tail views) (fun i => hviews i.succ))
      ((hviews 0).between (sameWorld D (Fin.tail views) (fun i => hviews i.succ))) (Rs 0)
      (representation D (Fin.tail views) (fun i => hviews i.succ) (fun i => Rs i.succ)) P
      (handles 0) (value (Fin.tail handles)) (hspec 0)
      (ih (Fin.tail views) (fun i => hviews i.succ) (fun i => Rs i.succ)
        (Fin.tail handles) (fun i => hspec i.succ))

end specification

end

end SampLib.LatentReal.CoordinateSum
