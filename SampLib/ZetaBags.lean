import SampLib.UniformVectorCoin
import SampLib.LatentCoinReciprocal
import Samplers.Constants.Special

/-! # The owned bag list used by the zeta coin

Allocation and conjunction execute the original raw-location list loops. The
joint posterior is retained across conjunction calls and reciprocal retries.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.ZetaBags

noncomputable section

@[pl_fold] def create {rT : Type} : Exp rT := pl%
  rec allocate remaining := if remaining = #0 then inl(#()) else
    let bag := &Occil.newUniformBag #();
    inr((bag, allocate (remaining - #1)))

@[pl_fold] def product {rT : Type} : Exp rT := pl%
  rec all xs := case! xs
    | inl(v) => #true
    | inr(p) => if &Occil.sampleGeometricBag (fst(p)) #() then all (snd(p)) else #false

private instance newBag_closed {rT : Type} : ClosedExp (Occil.newUniformBag : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.newUniformBag, Exp.fv]

private instance geometricBag_closed {rT : Type} :
    ClosedExp (Occil.sampleGeometricBag : Exp rT) where
  lc := by is_lc
  fv := by simp [Occil.sampleGeometricBag, Occil.uniformBagStep, Occil.newUniformBag,
    Occil.fairCoin, Exp.fv]

private instance create_closed {rT : Type} : ClosedExp (create : Exp rT) where
  lc := by is_lc
  fv := by simp [create, Occil.newUniformBag, Exp.fv]

private instance product_closed {rT : Type} : ClosedExp (product : Exp rT) where
  lc := by is_lc
  fv := by simp [product, Occil.sampleGeometricBag, Occil.uniformBagStep,
    Occil.newUniformBag, Occil.fairCoin, Exp.fv]

private theorem encode_cons {rT : Type} [ProbLangℝ rT] {n : ℕ} (l : Loc)
    (roots : Fin n → Loc) :
    (pl(inr((#loc l, {Exp.ofVal (listVal Val.loc (List.ofFn roots))}))) : Exp rT) =
      Exp.ofVal (listVal Val.loc (List.ofFn (Fin.cons l roots))) := by
  simp [Exp.ofVal, List.ofFn_succ, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open LatentReal LatentReal.LatentCoin UniformVector

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec

/-- The source allocation loop returns separate fresh roots, with no sampled bits. -/
theorem twp_create (E : CoPset) (n : ℕ) :
    ⊢ tglWp E pl(&(create : Exp rT) #int (n : ℤ))
      (fun v : Val rT => iprop(∃ roots : Fin n → Loc,
        ⌜v = listVal Val.loc (List.ofFn roots)⌝ ∗ rootsOwns roots (initial n))) := by
  induction n with
  | zero =>
    twp_pures
    twp_value
    imodintro
    iexists Fin.elim0
    isimp only [rootsOwns]
    ipureintro
    exact ⟨rfl, trivial⟩
  | succ n IH =>
    iterate 4 twp_pure
    twp_bind pl(&Occil.newUniformBag #())
    iapply tglWp_wand
    isplitl []
    · iapply UniformBag.twp_newUniformBag E
    iintro %v ⟨%l, %hv, Hhead⟩
    subst v
    iterate 2 twp_pure
    rw [Nat.cast_add_one, add_sub_cancel_right]
    twp_bind pl(&(create : Exp rT) #int (n : ℤ))
    iapply tglWp_wand
    isplitl []
    · iapply IH
    iintro %v ⟨%roots, %hv, Htail⟩
    subst v
    rw [encode_cons]
    iapply (tglWp_value (v := listVal Val.loc (List.ofFn (Fin.cons l roots))))
    iexists Fin.cons l roots
    isimp only [rootsOwns, initial, Fin.cons_zero, Fin.tail_cons, Fin.tail]
    have hprefix : Fin.tail (initial (n + 1)) = initial n := rfl
    rw [hprefix]
    iframe Hhead Htail

/-- Conjunction tests the actual list entries in order in the same latent world. -/
theorem twp_product (E : CoPset) {n : ℕ} (roots : Fin n → Loc)
    (indices : List (Fin n)) (p : Fin n → List Bool)
    (G : Bool → (Fin n → ℝ) → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    iprop(rootsOwns roots p ∗ ↯ (credit (world n) p (productBias indices) G)) ⊢
      tglWp E pl(&(product : Exp rT) {(listVal (fun i => Val.loc (roots i)) indices).fst})
        (post (world n) (fun _ => rootsOwns roots) Val.unit p G) := by
  induction indices generalizing p with
  | nil =>
    iintro ⟨Hstate, Hcredit⟩
    twp_pures
    twp_value
    imodintro
    isimp only [product_nil_credit] at Hcredit
    iapply post_return (world n) (fun _ => rootsOwns roots) Val.unit p p true G
      ((world n).refines_refl p)
    isimp only [world]
    iframe Hstate Hcredit
  | cons i indices IH =>
    iintro ⟨Hstate, Hcredit⟩
    isimp only [← product_expectation p i indices G] at Hcredit
    iterate 5 twp_pure
    twp_bind pl(&Occil.sampleGeometricBag #loc (roots i) #())
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply twp_coordinateCoin E roots p i (productInputCredit indices G)
        (measurable_productInputCredit indices G hG)
      iframe Hstate Hcredit
    iintro %v Hpost
    isimp only [post] at Hpost
    icases Hpost with ⟨%b, %q, %hb, Hstate, Hcredit⟩
    rcases hb with ⟨rfl, hpq⟩
    cases b
    · twp_pures
      twp_value
      imodintro
      isimp only [productInputCredit, Bool.false_eq_true, ite_false] at Hcredit
      iapply post_return (world n) (fun _ => rootsOwns roots) Val.unit p q false G hpq
      iframe Hstate Hcredit
    · iterate 2 twp_pure
      isimp only [productInputCredit, ite_true] at Hcredit
      iapply (tglWp_wand
        (Φ := post (world n) (fun _ => rootsOwns roots) Val.unit q G))
      isplitl [Hstate Hcredit]
      · ieval (
          change _ ⊢ tglWp E
            pl(&(product : Exp rT) {(listVal (fun i => Val.loc (roots i)) indices).fst}) _)
        iapply IH q
        isimp only [credit]
        iframe Hstate Hcredit
      iintro %v Hpost
      iapply post_weaken (world n) (fun _ => rootsOwns roots) Val.unit p q G v hpq $$ Hpost

end specification

end

end SampLib.ZetaBags
