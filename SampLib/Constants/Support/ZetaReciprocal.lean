import SampLib.Constants.Support.ZetaBags
import SampLib.Core.Syntax.ListValues

/-! # The reciprocal factory over the zeta coin's persistent bag list -/

open ProbLang
open scoped ENNReal

namespace SampLib.ZetaBags

noncomputable section

private instance product_closed {rT : Type} : ClosedExp (product : Exp rT) where
  lc := by is_lc
  fv := by simp [product, Occil.sampleGeometricBag, Occil.uniformBagStep,
    Occil.newUniformBag, Occil.fairCoin, Exp.fv]

private theorem listVal_map {rT α β : Type} [ProbLangℝ rT] (encode : β → Val rT)
    (f : α → β) (xs : List α) : listVal encode (xs.map f) = listVal (encode ∘ f) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, listVal, ih, Function.comp_apply]

private theorem roots_value {rT : Type} [ProbLangℝ rT] {n : ℕ} (roots : Fin n → Loc) :
    listVal (fun i => Val.loc (roots i)) (List.ofFn id) =
      (listVal Val.loc (List.ofFn roots) : Val rT) := by
  simpa only [List.map_ofFn, Function.comp_def, id_eq] using
    (listVal_map (Val.loc : Loc → Val rT) roots (List.ofFn id)).symm

/-- The callback closes over the original raw list, retaining every root across retries. -/
def productCallback {rT : Type} [ProbLangℝ rT] {n : ℕ} (roots : Fin n → Loc) : Val rT :=
  ⟨.lam (.app product (listVal Val.loc (List.ofFn roots)).fst),
    .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal LatentReal.LatentCoin UniformVector

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem post_source {n : ℕ} (roots : Fin n → Loc)
    (p : Fin n → List Bool) (G : Bool → (Fin n → ℝ) → ℝ≥0∞) (source : Val rT) :
    post (rT := rT) (GF := GF) (world n) (fun _ : Val rT => rootsOwns roots) Val.unit p G =
      post (rT := rT) (GF := GF) (world n) (fun _ : Val rT => rootsOwns roots) source p G := rfl

/-- Joint conditional product specification, without averaging before the next callback. -/
theorem product_coinSpec (E : CoPset) {n : ℕ} (roots : Fin n → Loc) :
    IsLatentCoinSpec (rT := rT) (GF := GF) E (world n) (fun _ : Val rT => rootsOwns roots)
      (productBias (List.ofFn id)) (fun _ => productCallback roots) where
  measurable_bias := measurable_productBias _
  spec source p G hG := by
    iintro H
    twp_pure
    have h := twp_product (rT := rT) (GF := GF) E roots (List.ofFn id) p G hG
    rw [roots_value, post_source roots p G source] at h
    iapply h $$ H

/-- The existing reciprocal factory uses the same joint world at every retry. -/
theorem twp_reciprocal (E : CoPset) {n : ℕ} (roots : Fin n → Loc)
    (p : Fin n → List Bool) (G : Bool → (Fin n → ℝ) → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) :
    iprop(rootsOwns roots p ∗
      ↯ (credit (world n) p (CoinReciprocal.bias (productBias (List.ofFn id))) G)) ⊢
      tglWp E pl(&Occil.oneDivOnePlus &(productCallback roots : Val rT).fst #())
        (post (world n) (fun _ : Val rT => rootsOwns roots) Val.unit p G) :=
  CoinReciprocal.twp_oneDivOnePlus E (world n) (fun _ : Val rT => rootsOwns roots)
    (productBias (List.ofFn id)) (fun _ => productCallback roots)
    (product_coinSpec E roots) Val.unit p G hG

end specification

end

end SampLib.ZetaBags
