import SampLib.UniformBagComparison

/-! # Exact comparisons with a shared cached uniform

Cached digits are consumed by finite induction. At an unsampled node, one of the
two fair children settles the comparison and the other receives twice the
termination credit. Every return retains the original bag and its posterior.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.UniformBag

noncomputable section

section ownership

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
variable {GF : BundledGFunctors} [AppGS rT GF] [ECGS GF]
local bi (IProp GF)

/-- The updated cache determines the returned comparison almost everywhere. -/
def lessPost (l : Loc) (p : List Bool) (x y : ℤ) (F : ℝ → ℝ≥0∞)
    (v : Val rT) : IProp GF := iprop(∃ (b : Bool) (q : List Bool),
  ⌜v = Val.bool b ∧ comparisonResult p x y b q⌝ ∗
  owns l q ∗ ↯ (DyadicPosterior.credit q F))

private theorem restore_less (l tail : Loc) (p q : List Bool) (head : Bool)
    (x y : ℤ) (hy : 0 < y) (hs : stepRefines p head q)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (v : Val rT) :
    iprop(appHeapFrag l (nodeVal head tail) ∗
      lessPost tail q (tailNumerator x y head) y
        (fun u => F (DyadicPosterior.half head u)) v) ⊢ lessPost l p x y F v := by
  iintro ⟨Hl, Htail⟩
  isimp only [lessPost] at Htail
  ihave ⟨%b, %r, %hr, Htail, Hcredit⟩ := Htail
  isimp only [lessPost]
  iexists b, head :: r
  isimp only [← DyadicPosterior.credit_cons head r F hF] at Hcredit
  ihave Hbag : owns l (head :: r) $$ [Hl Htail]
  · isimp only [owns]
    iexists tail
    iframe Hl Htail
  iframe Hbag Hcredit
  ipureintro
  exact ⟨hr.1, comparisonResult_tail hs hy hr.2⟩

private theorem return_less (l : Loc) (p : List Bool) (x y : ℤ) (b : Bool)
    (F : ℝ → ℝ≥0∞) (h : DyadicPosterior.resolves p ((x : ℝ) / y) b) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      lessPost l p x y F (Val.bool b) := by
  iintro ⟨Hbag, Hcredit⟩
  isimp only [lessPost]
  iexists b, p
  iframe Hbag Hcredit
  ipureintro
  exact ⟨rfl, List.prefix_refl _, h⟩

private theorem return_step (l tail : Loc) (p q : List Bool) (x y : ℤ) (b : Bool)
    (hy : 0 < y) (hs : stepRefines p b q) (hb : b ≠ retryBit x y)
    (F : ℝ → ℝ≥0∞) :
    iprop(appHeapFrag l (nodeVal b tail) ∗ owns tail q ∗
      ↯ (DyadicPosterior.credit (b :: q) F)) ⊢ lessPost l p x y F (Val.bool (!b)) := by
  iintro ⟨Hl, Htail, Hcredit⟩
  isimp only [lessPost]
  iexists !b, b :: q
  ihave Hbag : owns l (b :: q) $$ [Hl Htail]
  · isimp only [owns]
    iexists tail
    iframe Hl Htail
  iframe Hbag Hcredit
  ipureintro
  refine ⟨rfl, ?_, exit_resolves q x y hy b hb⟩
  rcases hs with ⟨rfl, _⟩ | rfl
  · exact List.nil_prefix
  · exact List.prefix_refl _

end ownership

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def freshProperty (E : CoPset) : IProp GF := iprop(
  ∀ (l : Loc) (x y : ℤ), ⌜0 < y⌝ -∗ ∀ F : ℝ → ℝ≥0∞, ⌜Measurable F⌝ -∗
    owns l [] -∗ ↯ (DyadicPosterior.credit [] F) -∗
      tglWp E pl(&Occil.uniformBagLess #loc l #int x #int y) (lessPost l [] x y F))

private theorem twp_freshProperty (E : CoPset) (ε : ℝ≥0∞) (hε : 0 < ε) :
    iprop(↯ ε) ⊢ freshProperty (GF := GF) E := by
  iintro Hterm
  iapply ErrorCredit.Induction.simple (k := 2) hε (by norm_num) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩
  isimp only [freshProperty]
  iintro %l %x %y %hy %F %hF Hbag Hcredit
  isimp only [ENNReal.coe_ofNat] at IH
  iterate 5 twp_pure
  rw [show decide (y ≤ 0) = false from decide_eq_false (not_le.mpr hy)]
  twp_pure
  twp_pure
  by_cases hx : x ≤ 0
  · rw [decide_eq_true hx]
    twp_pures
    twp_value
    imodintro
    iapply return_less l [] x y false F (resolves_nonpos [] x y hx hy)
    iframe Hbag Hcredit
  · rw [decide_eq_false hx]
    twp_pure
    twp_pure
    by_cases hxy : y ≤ x
    · rw [decide_eq_true hxy]
      twp_pures
      twp_value
      imodintro
      iapply return_less l [] x y true F (resolves_ge [] x y hxy hy)
      iframe Hbag Hcredit
    · rw [decide_eq_false hxy]
      twp_pure
      simp only [uniformBagStep_openRec, uniformBagStep_closeRec]
      twp_bind pl(&Occil.uniformBagStep #loc l)
      icombine Hcredit Hterm as Htotal
      isimp only [← comparison_expectation F hF (retryBit x y) ε] at Htotal
      iapply tglWp_wand
      isplitl [Hbag Htotal]
      · iapply twp_freshStep E l (comparisonCredit F (retryBit x y) ε)
        iframe Hbag Htotal
      iintro %v ⟨%b, %tail, %hv, Hl, Htail, Hcredit⟩
      subst v
      cases b <;> iterate 6 twp_pure
      · by_cases ht : 2 * x < y
        · rw [decide_eq_true ht]
          twp_pure
          twp_pure
          isimp only [comparisonCredit, retryBit, decide_eq_false (not_le.mpr ht),
            ite_true, DyadicPosterior.credit_cons false [] F hF] at Hcredit
          ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
          twp_bind pl(&Occil.uniformBagLess #loc tail #int (2 * x) #int y)
          iapply tglWp_wand
          isplitl [Htail Hcredit Hterm IH]
          · ihave Hnext := IH $$ Hterm
            isimp only [freshProperty] at Hnext
            iapply Hnext $$ %tail %(2 * x) %y %hy
              %(fun u => F (DyadicPosterior.half false u))
              %(hF.comp (DyadicPosterior.measurable_half false)) Htail Hcredit
          iintro %v Hnext
          iapply (tglWp_value (v := v))
          iapply restore_less l tail [] [] false x y hy (Or.inl ⟨rfl, rfl⟩) F hF v
          isimp only [tailNumerator, Bool.false_eq_true, ite_false, sub_zero]
          iframe Hl Hnext
        · rw [decide_eq_false ht]
          twp_pures
          isimp only [comparisonCredit, retryBit, decide_eq_true (le_of_not_gt ht),
            Bool.false_eq_true, ite_false, add_zero] at Hcredit
          twp_value
          imodintro
          have hreturn := return_step (rT := rT) (GF := GF)
            l tail [] [] x y false hy (Or.inl ⟨rfl, rfl⟩)
            (by simp [retryBit, le_of_not_gt ht]) F
          simp only [Bool.not_false] at hreturn
          iapply hreturn
          iframe Hl Htail Hcredit
      · by_cases ht : 2 * x < y
        · rw [decide_eq_true ht]
          twp_pures
          isimp only [comparisonCredit, retryBit, decide_eq_false (not_le.mpr ht),
            Bool.true_eq_false, ite_false, add_zero] at Hcredit
          twp_value
          imodintro
          have hreturn := return_step (rT := rT) (GF := GF)
            l tail [] [] x y true hy (Or.inl ⟨rfl, rfl⟩)
            (by simp [retryBit, not_le.mpr ht]) F
          simp only [Bool.not_true] at hreturn
          iapply hreturn
          iframe Hl Htail Hcredit
        · rw [decide_eq_false ht]
          iterate 3 twp_pure
          isimp only [comparisonCredit, retryBit, decide_eq_true (le_of_not_gt ht),
            ite_true, DyadicPosterior.credit_cons true [] F hF] at Hcredit
          ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
          twp_bind pl(&Occil.uniformBagLess #loc tail #int (2 * x - y) #int y)
          iapply tglWp_wand
          isplitl [Htail Hcredit Hterm IH]
          · ihave Hnext := IH $$ Hterm
            isimp only [freshProperty] at Hnext
            iapply Hnext $$ %tail %(2 * x - y) %y %hy
              %(fun u => F (DyadicPosterior.half true u))
              %(hF.comp (DyadicPosterior.measurable_half true)) Htail Hcredit
          iintro %v Hnext
          iapply (tglWp_value (v := v))
          iapply restore_less l tail [] [] true x y hy (Or.inl ⟨rfl, rfl⟩) F hF v
          isimp only [tailNumerator, ite_true]
          iframe Hl Hnext

private theorem twp_freshLess (E : CoPset) (l : Loc) (x y : ℤ) (hy : 0 < y)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns l [] ∗ ↯ (DyadicPosterior.credit [] F)) ⊢
      tglWp E pl(&Occil.uniformBagLess #loc l #int x #int y) (lessPost l [] x y F) := by
  iintro ⟨Hbag, Hcredit⟩
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  ihave Hnext := twp_freshProperty E ε hε $$ Hterm
  isimp only [freshProperty] at Hnext
  iapply Hnext $$ %l %x %y %hy %F %hF Hbag Hcredit

/-- Compare with any rational threshold while retaining the complete shared cache. -/
theorem twp_uniformBagLess (E : CoPset) (l : Loc) (p : List Bool) (x y : ℤ)
    (hy : 0 < y) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    iprop(owns l p ∗ ↯ (DyadicPosterior.credit p F)) ⊢
      tglWp E pl(&Occil.uniformBagLess #loc l #int x #int y) (lessPost l p x y F) := by
  induction p generalizing l x y F with
  | nil => exact twp_freshLess E l x y hy F hF
  | cons head p IH =>
    iintro ⟨Hbag, Hcredit⟩
    iterate 5 twp_pure
    rw [show decide (y ≤ 0) = false from decide_eq_false (not_le.mpr hy)]
    twp_pure
    twp_pure
    by_cases hx : x ≤ 0
    · rw [decide_eq_true hx]
      twp_pures
      twp_value
      imodintro
      iapply return_less l (head :: p) x y false F (resolves_nonpos _ x y hx hy)
      iframe Hbag Hcredit
    · rw [decide_eq_false hx]
      twp_pure
      twp_pure
      by_cases hxy : y ≤ x
      · rw [decide_eq_true hxy]
        twp_pures
        twp_value
        imodintro
        iapply return_less l (head :: p) x y true F (resolves_ge _ x y hxy hy)
        iframe Hbag Hcredit
      · rw [decide_eq_false hxy]
        twp_pure
        isimp only [uniformBagStep_openRec, uniformBagStep_closeRec]
        twp_bind pl(&Occil.uniformBagStep #loc l)
        iapply tglWp_wand
        isplitl [Hbag Hcredit]
        · iapply twp_uniformBagStep E l (head :: p) F hF
          iframe Hbag Hcredit
        iintro %v ⟨%b, %tail, %q, %hv, Hl, Htail, Hcredit⟩
        rcases hv with ⟨rfl, hstep⟩
        have hbq : head = b ∧ p = q := by simpa [stepRefines] using hstep
        rcases hbq with ⟨rfl, rfl⟩
        cases head <;> iterate 6 twp_pure
        · by_cases ht : 2 * x < y
          · rw [decide_eq_true ht]
            twp_pure
            twp_pure
            isimp only [DyadicPosterior.credit_cons false p F hF] at Hcredit
            twp_bind pl(&Occil.uniformBagLess #loc tail #int (2 * x) #int y)
            iapply tglWp_wand
            isplitl [Htail Hcredit]
            · iapply IH tail (2 * x) y hy
                (fun u => F (DyadicPosterior.half false u))
                (hF.comp (DyadicPosterior.measurable_half false))
              iframe Htail Hcredit
            iintro %v Hnext
            iapply (tglWp_value (v := v))
            iapply restore_less l tail (false :: p) p false x y hy hstep F hF v
            isimp only [tailNumerator, Bool.false_eq_true, ite_false, sub_zero]
            iframe Hl Hnext
          · rw [decide_eq_false ht]
            twp_pures
            twp_value
            imodintro
            have hreturn := return_step (rT := rT) (GF := GF)
              l tail (false :: p) p x y false hy hstep
              (by simp [retryBit, le_of_not_gt ht]) F
            simp only [Bool.not_false] at hreturn
            iapply hreturn
            iframe Hl Htail Hcredit
        · by_cases ht : 2 * x < y
          · rw [decide_eq_true ht]
            twp_pures
            twp_value
            imodintro
            have hreturn := return_step (rT := rT) (GF := GF) l tail (true :: p) p x y true hy hstep
              (by simp [retryBit, not_le.mpr ht]) F
            simp only [Bool.not_true] at hreturn
            iapply hreturn
            iframe Hl Htail Hcredit
          · rw [decide_eq_false ht]
            iterate 3 twp_pure
            isimp only [DyadicPosterior.credit_cons true p F hF] at Hcredit
            twp_bind pl(&Occil.uniformBagLess #loc tail #int (2 * x - y) #int y)
            iapply tglWp_wand
            isplitl [Htail Hcredit]
            · iapply IH tail (2 * x - y) y hy
                (fun u => F (DyadicPosterior.half true u))
                (hF.comp (DyadicPosterior.measurable_half true))
              iframe Htail Hcredit
            iintro %v Hnext
            iapply (tglWp_value (v := v))
            iapply restore_less l tail (true :: p) p true x y hy hstep F hF v
            isimp only [tailNumerator, ite_true]
            iframe Hl Hnext

end specification

end

end SampLib.UniformBag
