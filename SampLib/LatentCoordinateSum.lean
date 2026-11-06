import SampLib.LatentCoordinateSumModel
import SampLib.LatentVectorSpec
import SampLib.Syntax.PSRNCoordinateSum

/-! # Constructing and observing a common sum without duplicating its latent world -/

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
