import SampLib.Samplers.PSRNExpMinusCoin

open ProbLang
open scoped ENNReal

namespace PSRNExpMinusCoinAuthorCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

private theorem rational_domain (a : ℤ) (ha : 0 ≤ a) :
    ExpMinusCoin.Admissible (LatentRational.model a 1) () := by
  constructor
  · simp [LatentRational.model, ha]
  · right
    simp [LatentRational.model]


variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangDist.IsUniformInt ℝ]
  [ProbLangFFI ℝ] [ProbLangObs ℝ]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val ℝ) (s : S) (G : Bool → Ω → ℝ≥0∞)
    (hG : ∀ b, Measurable (G b)) (R : IProp GF) :
    ⊢ ExpMinusCoin.domainOwns D owns source s ∗
        ↯ (LatentCoin.credit D s (ExpMinusCoin.bias D) G) ∗ R -∗
      tglWp E pl(&Occil.PSRN.expMinusCoin &source.fst #())
        (fun result => iprop(∃ (b : Bool) (t : S),
          ⌜result = Val.bool b ∧ D.refines s t⌝ ∗
          ExpMinusCoin.domainOwns D owns source t ∗
          ↯ (∫⁻ x, G b x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  iapply (ExpMinusCoin.expMinusCoin_programSpec E D hD owns horacle).wp source s G hG _ $$
    Hstate Hcredit
  iintro %b %t %ht Hstate Hcredit
  iexists b, t
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, ht⟩

example (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (owns : Val ℝ → S → IProp GF) (horacle : IsOracleSpec E D owns) :
    IsLatentCoinSpec E D (ExpMinusCoin.domainOwns D owns) (ExpMinusCoin.bias D)
      ExpMinusCoin.Program.callback :=
  ExpMinusCoin.expMinusCoin_coinSpec E D hD owns horacle


example : ¬ Floor.AvoidsGrid (LatentRational.model 0 1) 1 () := by
  simp [Floor.AvoidsGrid, Floor.output, LatentRational.model]

example : ExpMinusCoin.Admissible (LatentRational.model 0 1) () := rational_domain 0 le_rfl

example : ¬ ExpMinusCoin.Admissible (LatentRational.model (-1) 1) () := by
  simp [ExpMinusCoin.Admissible, LatentRational.model]

example (x : ℝ) (hx : 0 ≤ x) : (ExpMinusCoin.valueBias x : ℝ) = Real.exp (-x) :=
  ExpMinusCoin.valueBias_coe hx

example : ExpMinusCoin.valueBias 0 = 1 := by
  apply Subtype.ext
  norm_num [ExpMinusCoin.valueBias]

example (D : Model Ω S) (s t : S) (hs : ExpMinusCoin.Admissible D s)
    (hst : D.refines s t) : ExpMinusCoin.Admissible D t := hs.refines hst

example (p : unitInterval) : RealCoin.credit p (fun _ => ∞) = ∞ := by
  rw [← RealCoin.lintegral_law]
  simp [-Bool.univ_eq]

example (E : CoPset) (G : Bool → Unit → ℝ≥0∞) (hG : ∀ b, Measurable (G b)) :
    ⊢ ↯ (G true ()) -∗
      tglWp E pl(&Occil.PSRN.expMinusCoin &(LatentRational.value 0 1 : Val ℝ).fst #())
        (LatentCoin.post (LatentRational.model 0 1) (LatentRational.owns 0 1)
          (LatentRational.value 0 1) () G) := by
  have hcredit : LatentCoin.credit (LatentRational.model 0 1) ()
      (ExpMinusCoin.bias (LatentRational.model 0 1)) G = G true () := by
    simp [LatentCoin.credit, LatentCoin.kernel, ExpMinusCoin.bias, ExpMinusCoin.valueBias,
      LatentRational.model, RealCoin.credit, RealCoin.pmf]
  iintro Hcredit
  iapply ExpMinusCoin.twp_expMinusCoin E (LatentRational.model 0 1)
    (by intro n; exact measurable_const) (LatentRational.owns 0 1)
    (LatentRational.oracleSpec E 0 1 (by norm_num)) (LatentRational.value 0 1) ()
    (rational_domain 0 le_rfl) G hG
  isplitl []
  · isimp only [LatentRational.owns]
    ipureintro
    trivial
  isimp only [hcredit]
  iexact Hcredit

end

end PSRNExpMinusCoinAuthorCallers

#print axioms SampLib.LatentReal.Floor.twp_floorScaled_exact
#print axioms SampLib.LatentReal.ExpMinusCoin.expectation
#print axioms SampLib.LatentReal.ExpMinusCoin.Program.source_eq
#print axioms SampLib.LatentReal.ExpMinusCoin.twp_expMinusCoin
#print axioms SampLib.LatentReal.ExpMinusCoin.expMinusCoin_programSpec
#print axioms SampLib.LatentReal.ExpMinusCoin.expMinusCoin_coinSpec
