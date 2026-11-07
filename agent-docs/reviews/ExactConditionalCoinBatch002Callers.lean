import SampLib.PSRN.PSRNExpMinusCoin
import SampLib.PSRN.Support.Arithmetic.Rational

open ProbLang
open scoped ENNReal SampLib.LatentReal.ExpMinusCoin.Program

namespace ReviewExactConditionalCoin002

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def twice (e : Exp ℝ) : Exp ℝ :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) e)) e

/-- Two trials keep their joint latent dependency; only their auxiliary randomness is fresh. -/
theorem repeated (E : CoPset) (D : Model Ω S) (owns : Val ℝ → S → IProp GF)
    (φ : Ω → unitInterval) (program : Val ℝ → Exp ℝ)
    (h : IsLatentCoinProgramSpec E D owns φ program) (source : Val ℝ)
    (he : (program source).IsLocallyClosed) (s : S)
    (H : Bool → Bool → Ω → ℝ≥0∞) (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s φ
      (fun b => LatentCoin.kernel φ (H b))) ∗ R) ⊢
      tglWp E (twice (program source)) (fun v : Val ℝ => iprop(∃ b c t,
        ⌜v = Val.pair (Val.bool b) (Val.bool c) ∧ D.refines s t⌝ ∗
        owns source t ∗ ↯ (∫⁻ x, H b c x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold twice
  twp_bind (program source)
  iapply h.wp source s (fun b => LatentCoin.kernel φ (H b))
    (fun b => LatentCoin.measurable_kernel h.measurable_bias (hH b)) _ $$ Hstate Hcredit
  iintro %b %t %hst Hstate Hcredit
  twp_pure
  rw [← Exp.open_lc 0 (Val.bool b).fst (program source) he]
  twp_bind (program source)
  have hbudget : (∫⁻ x, LatentCoin.kernel φ (H b) x ∂D.posterior t) =
      LatentCoin.credit D t φ (H b) := rfl
  isimp only [hbudget] at Hcredit
  iapply h.wp source t (H b) (hH b) _ $$ Hstate Hcredit
  iintro %c %u %htu Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  iexists b, c, u
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, D.refines_trans hst htu⟩

section source

variable [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ]

example (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (v : Val ℝ) (s : S) (H : Bool → Bool → Ω → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :=
  repeated E D (ExpMinusCoin.domainOwns D owns) (ExpMinusCoin.bias D)
    (fun source => pl(&Occil.PSRN.expMinusCoin &source.fst #()))
    (ExpMinusCoin.expMinusCoin_programSpec E D hD owns horacle) v (by is_lc) s H hH R

omit [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ] in
private theorem zero_admissible : ExpMinusCoin.Admissible (LatentRational.model 0 1) () := by
  constructor
  · exact Filter.Eventually.of_forall fun _ => by norm_num [LatentRational.model]
  · right
    exact Filter.Eventually.of_forall fun _ => rfl

omit [ProbLangDist ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
  [ProbLangDist.IsUniformInt ℝ] [ProbLangDist.IsUniformReal ℝ] in
private theorem half_admissible : ExpMinusCoin.Admissible (LatentRational.model 1 2) () := by
  constructor
  · exact Filter.Eventually.of_forall fun _ => by norm_num [LatentRational.model]
  · left
    exact Filter.Eventually.of_forall fun _ => by
      norm_num [Floor.output, LatentRational.model]

example (E : CoPset) (H : Bool → Bool → Unit → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :=
  repeated E (LatentRational.model 0 1)
    (ExpMinusCoin.domainOwns (LatentRational.model 0 1) (LatentRational.owns 0 1))
    (ExpMinusCoin.bias (LatentRational.model 0 1))
    (fun source => pl(&Occil.PSRN.expMinusCoin &source.fst #()))
    (ExpMinusCoin.expMinusCoin_programSpec E (LatentRational.model 0 1)
      (fun _ => measurable_const) (LatentRational.owns 0 1)
      (LatentRational.oracleSpec E 0 1 (by decide)))
    (LatentRational.value 0 1) (by is_lc) () H hH R

example (E : CoPset) (R : IProp GF) :=
  repeated E (LatentRational.model 1 2)
    (ExpMinusCoin.domainOwns (LatentRational.model 1 2) (LatentRational.owns 1 2))
    (ExpMinusCoin.bias (LatentRational.model 1 2))
    (fun source => pl(&Occil.PSRN.expMinusCoin &source.fst #()))
    (ExpMinusCoin.expMinusCoin_programSpec E (LatentRational.model 1 2)
      (fun _ => measurable_const) (LatentRational.owns 1 2)
      (LatentRational.oracleSpec E 1 2 (by decide)))
    (LatentRational.value 1 2) (by is_lc) () (fun _ _ _ => ∞)
    (fun _ _ => measurable_const) R

/-- The admitted exact grid atom supplies the real program from its actual point oracle. -/
theorem actual_zero (E : CoPset) (G : Bool → Unit → ℝ≥0∞) (R : IProp GF) :
    iprop(↯ (G true ()) ∗ R) ⊢
      tglWp E pl(&Occil.PSRN.expMinusCoin &(LatentRational.value (rT := ℝ) 0 1).fst #())
        (fun result : Val ℝ => iprop(LatentCoin.post (LatentRational.model 0 1)
          (ExpMinusCoin.domainOwns (LatentRational.model 0 1) (LatentRational.owns 0 1))
          (LatentRational.value 0 1) () G result ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply (ExpMinusCoin.expMinusCoin_programSpec E (LatentRational.model 0 1)
      (fun _ => measurable_const) (LatentRational.owns 0 1)
      (LatentRational.oracleSpec E 0 1 (by decide))).spec
      (LatentRational.value 0 1) () G (fun _ => measurable_of_countable _)
    isplitl []
    · isimp only [ExpMinusCoin.domainOwns, LatentRational.owns]
      isplit
      · ipureintro
        exact zero_admissible
      · ipureintro
        trivial
    isimp [LatentCoin.credit, LatentCoin.kernel, ExpMinusCoin.bias,
      ExpMinusCoin.valueBias, LatentRational.model, RealCoin.credit, RealCoin.pmf]
    iframe Hcredit
  iintro %v Hpost
  iframe Hpost HR

example (E : CoPset) (R : IProp GF) := actual_zero E (fun b _ => if b then 0 else ∞) R

end source

example : Floor.AvoidsGrid (LatentRational.model 0 1) 1 () = False := by
  simp [Floor.AvoidsGrid, Floor.output, LatentRational.model]

example : ExpMinusCoin.Admissible (LatentRational.model 0 1) () := zero_admissible
example : ExpMinusCoin.Admissible (LatentRational.model 1 2) () := half_admissible

#print axioms SampLib.LatentReal.ExpMinusCoin.expMinusCoin_programSpec
#print axioms SampLib.LatentReal.ExpMinusCoin.expMinusCoin_coinSpec
#print axioms SampLib.LatentReal.ExpMinusCoin.expectation
#print axioms SampLib.LatentReal.Floor.twp_floorScaled_exact
#print axioms repeated
#print axioms actual_zero

end
end ReviewExactConditionalCoin002
