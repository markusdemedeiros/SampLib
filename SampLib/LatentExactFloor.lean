import SampLib.PSRNFloor

/-! # Exact first-read floor observations, including integer atoms

Zero enclosure error makes both endpoints equal. The unchanged floor program
therefore resolves in one read, without any integer-grid avoidance assumption.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Floor

noncomputable section

private theorem resolves_exact {Ω S : Type} [MeasurableSpace Ω]
    (D : Model Ω S) (s : S) (n : ℕ) (hzero : ∀ᵐ x ∂D.posterior s, D.error n x = 0)
    (I : RationalInterval) (hI : D.Encloses s n I) (scale : ℤ) :
    I.lowerFloor scale = I.upperFloor scale := by
  obtain ⟨x, hx, hzero⟩ := (hI.and hzero).exists
  have heq : I.lowerReal = I.upperReal :=
    le_antisymm I.lowerReal_le_upperReal (by linarith [hx.2])
  rw [I.lowerFloor_eq, I.upperFloor_eq, heq]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

omit [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT] in
private theorem int_beq (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

/-- A zero-error first read resolves even when the represented value is an integer. -/
theorem twp_floorScaled_exact_view (E : CoPset) (D : Model Ω S)
    (P : S → IProp GF) (source : Val rT) (hsource : IsViewSpec E D P source)
    (scale : ℤ) (hscale : 0 < scale) (s : S)
    (hzero : ∀ᵐ x ∂D.posterior s, D.error 1 x = 0)
    (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    iprop(P s ∗ ↯ (∫⁻ x, outputCredit D scale G x ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #scale) (post D scale P s G) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply Program.twp_open E source scale hscale
  iterate 2 twp_pure
  twp_bind pl(&source.fst #1)
  iapply hsource.wp s 1 (outputCredit D scale G) (measurable_outputCredit D scale G hG) _ $$
    Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  have heq := resolves_exact D t 1 ((D.absolutelyContinuous hI.1).ae_le hzero) I hI.2 scale
  have hresolve := resolves D t 1 scale hscale.le I hI.2 heq
  have hcredit : (∫⁻ x, outputCredit D scale G x ∂D.posterior t) =
      ∫⁻ x, G (I.lowerFloor scale) x ∂D.posterior t := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hresolve] with x hx
    simp only [outputCredit, hx]
  iterate 14 twp_pure
  simp only [int_beq]
  rw [show (I.lower * scale / I.denominator == I.upper * scale / I.denominator) = true
    from beq_iff_eq.mpr heq]
  twp_pure
  twp_value
  imodintro
  isimp only [post]
  iexists I.lowerFloor scale, t
  isimp only [hcredit] at Hcredit
  iframe Hstate Hcredit
  ipureintro
  exact ⟨rfl, hI.1, hresolve⟩

/-- An ordinary exact oracle supplies the same endpoint-inclusive floor contract. -/
theorem twp_floorScaled_exact (E : CoPset) (D : Model Ω S)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (scale : ℤ) (hscale : 0 < scale) (s : S)
    (hzero : ∀ᵐ x ∂D.posterior s, D.error 1 x = 0)
    (G : ℤ → Ω → ℝ≥0∞) (hG : ∀ z, Measurable (G z)) :
    iprop(owns source s ∗ ↯ (∫⁻ x, outputCredit D scale G x ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.floorScaled &source.fst #scale)
        (post D scale (owns source) s G) :=
  twp_floorScaled_exact_view E D (owns source) source (horacle.viewSpec E D owns source)
    scale hscale s hzero G hG

end specification

end

end SampLib.LatentReal.Floor
