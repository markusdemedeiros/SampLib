import SampLib.PSRN.Laws.FloorKernel
import SampLib.PSRN.Syntax.PSRNFloor

/-! # Exact floor observations of an owned deferred real

Each read retains the same joint latent world. Almost-sure avoidance of the
scaled integer grid supplies a finite proof horizon for the actual retry loop.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Floor

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem int_beq (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

/-- An observed integer retains both its source state and arbitrary joint credit. -/
def post (D : Model Ω S) (scale : ℤ) (P : S → IProp GF) (initial : S)
    (G : ℤ → Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ (z : ℤ) (t : S),
    ⌜result = Val.int z ∧ D.refines initial t ∧
      ∀ᵐ x ∂D.posterior t, output D scale x = z⌝ ∗
    P t ∗ ↯ (∫⁻ x, G z x ∂D.posterior t))

private theorem twp_round (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (scale : ℤ) (hscale : 0 < scale) (initial s : S) (hs : D.refines initial s)
    (N n : ℕ) (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z))
    (hcontinue : ∀ (t : S) (I : RationalInterval), D.refines s t → D.Encloses t n I →
      I.lowerFloor scale ≠ I.upperFloor scale →
      iprop(P t ∗ ↯ (∫⁻ x, horizonCredit D scale N G x ∂D.posterior t)) ⊢
        tglWp E pl(&(Program.loop source scale) #int ((n + 1 : ℕ) : ℤ))
          (post D scale P initial G)) :
    iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D scale N G x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.loop source scale) #int (n : ℤ))
        (post D scale P initial G) := by
  iintro ⟨Hstate, Hcredit⟩
  iterate 2 twp_pure
  twp_bind pl(&source.fst #int (n : ℤ))
  iapply hsource.wp s n (horizonCredit D scale N G)
    (measurable_horizonCredit D hD scale N G hG) _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  iterate 14 twp_pure
  simp only [int_beq]
  by_cases hresolved : I.lowerFloor scale = I.upperFloor scale
  · rw [show (I.lower * scale / I.denominator == I.upper * scale / I.denominator) = true
      from beq_iff_eq.mpr hresolved]
    twp_pure
    twp_value
    imodintro
    isimp only [post]
    iexists I.lowerFloor scale, t
    have hresolve := resolves D t n scale hscale.le I hI.2 hresolved
    ihave Hcredit := ErrorCredit.weaken
      (return_credit D t scale N G (I.lowerFloor scale) hresolve) $$ Hcredit
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, D.refines_trans hs hI.1, hresolve⟩
  · rw [show (I.lower * scale / I.denominator == I.upper * scale / I.denominator) = false
      from beq_eq_false_iff_ne.mpr hresolved]
    iterate 2 twp_pure
    rw [← Nat.cast_add_one]
    twp_bind pl(&(Program.loop source scale) #int ((n + 1 : ℕ) : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply hcontinue t I hI.1 hI.2 hresolved
    iframe Hstate Hcredit

private theorem twp_until (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (scale : ℤ) (hscale : 0 < scale) (initial s : S) (hs : D.refines initial s)
    (N n : ℕ) (hn : n ≤ N) (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D scale N G x ∂D.posterior s)) ⊢
      tglWp E pl(&(Program.loop source scale) #int (n : ℤ))
        (post D scale P initial G) := by
  have hall : ∀ n ≤ N, ∀ s, D.refines initial s →
      iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D scale N G x ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.loop source scale) #int (n : ℤ))
          (post D scale P initial G) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ s, D.refines initial s →
      iprop(P s ∗ ↯ (∫⁻ x, horizonCredit D scale N G x ∂D.posterior s)) ⊢
        tglWp E pl(&(Program.loop source scale) #int (n : ℤ))
          (post D scale P initial G)) ?_ ?_ hn
    · intro n hn IH s hs
      iapply twp_round E D hD P source hsource scale hscale initial s hs N n G hG
        (fun t _ hst _ _ => IH t (D.refines_trans hs hst))
    · intro s hs
      iapply twp_round E D hD P source hsource scale hscale initial s hs N N G hG ?_
      intro t I hst hI hunresolved
      iintro ⟨Hstate, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict
        (unresolved_credit D t scale hscale.le N G I hI hunresolved) $$ Hcredit
  exact hall n hn s hs

/-- The actual floor constructor preserves shared ownership and resolves the scaled integer. -/
theorem twp_floorScaled_view (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (scale : ℤ) (hscale : 0 < scale) (s : S) (hgrid : AvoidsGrid D scale s)
    (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    iprop(P s ∗ ↯ (∫⁻ x, outputCredit D scale G x ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #scale) (post D scale P s G) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply Program.twp_open E source scale hscale _
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN, hcost⟩ := exists_horizon D s hD scale hgrid 1 G hG δ hδ
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hcost $$ Htotal
  iapply twp_until E D hD P source hsource scale hscale s s (D.refines_refl s)
    N 1 hN G hG
  iframe Hstate Hcredit

/-- An ordinary oracle can be observed as a shared view of its own physical state. -/
theorem twp_floorScaled (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (scale : ℤ) (hscale : 0 < scale) (s : S)
    (hgrid : AvoidsGrid D scale s) (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    iprop(owns source s ∗ ↯ (∫⁻ x, outputCredit D scale G x ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #scale)
        (post D scale (owns source) s G) :=
  twp_floorScaled_view E D hD (owns source) source (horacle.viewSpec E D owns source)
    scale hscale s hgrid G hG

end

end SampLib.LatentReal.Floor
