import SampLib.PSRN.Support.PSRNCoin
import SampLib.PSRN.Support.Arithmetic.Rational
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Metrology.TotalEris.Examples.Samplers.RealDecrTrial

open ProbLang
open scoped ENNReal

namespace ReviewExactConditionalCoin001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

private def twice (e : Exp rT) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) e)) e

/-- Two trials keep their joint latent dependency; only their auxiliary randomness is fresh. -/
theorem repeated (E : CoPset) (D : Model Ω S) (owns : Val rT → S → IProp GF)
    (φ : Ω → unitInterval) (program : Val rT → Exp rT)
    (h : IsLatentCoinProgramSpec E D owns φ program) (source : Val rT)
    (he : (program source).IsLocallyClosed) (s : S)
    (H : Bool → Bool → Ω → ℝ≥0∞) (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :
    iprop(owns source s ∗ ↯ (LatentCoin.credit D s φ
      (fun b => LatentCoin.kernel φ (H b))) ∗ R) ⊢
      tglWp E (twice (program source)) (fun v : Val rT => iprop(∃ b c t,
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

omit [MeasurableSpace rT] [LawfulProbLangℝ rT] [ProbLangDist rT]
  [ProbLangFFI rT] [ProbLangObs rT] in
private theorem coin_lc (source : Val rT) :
    (pl(&Occil.PSRN.coin &source.fst #()) : Exp rT).IsLocallyClosed := by
  rw [Coin.Program.source_eq]
  have hc := Coin.Program.source_lc (rT := rT)
  is_lc

section concrete

variable [ProbLangDist.IsUniformInt rT]

example (E : CoPset) (D : Model Ω S) (herror : D.MeasurableError)
    (owns : Val rT → S → IProp GF) (horacle : IsOracleSpec E D owns)
    (source : Val rT) (s : S) (H : Bool → Bool → Ω → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :=
  repeated E D owns (fun x => LatentBernoulli.bias (D.value x))
    (fun v => pl(&Occil.PSRN.coin &v.fst #()))
    (Coin.coin_programSpec E D herror owns horacle) source (coin_lc source) s H hH R

/-- The two input trials share the very same cached uniform real. -/
example (E : CoPset) (source : Val rT) (p : List Bool)
    (H : Bool → Bool → ℝ → ℝ≥0∞) (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :=
  repeated E LatentUniform.model LatentUniform.owns
    (fun x => LatentBernoulli.bias (LatentUniform.model.value x))
    (fun v => pl(&Occil.PSRN.coin &v.fst #()))
    (Coin.coin_programSpec E LatentUniform.model (fun _ => measurable_const)
      LatentUniform.owns (LatentUniform.oracleSpec E)) source (coin_lc source) p H hH R

/-- Out-of-range atomic values clamp exactly at either endpoint. -/
example (E : CoPset) (a : ℤ) (H : Bool → Bool → Unit → ℝ≥0∞)
    (hH : ∀ b c, Measurable (H b c)) (R : IProp GF) :=
  repeated E (LatentRational.model a 1) (LatentRational.owns a 1)
    (fun x => LatentBernoulli.bias ((LatentRational.model a 1).value x))
    (fun v => pl(&Occil.PSRN.coin &v.fst #()))
    (Coin.coin_programSpec E (LatentRational.model a 1) (fun _ => measurable_const)
      (LatentRational.owns a 1) (LatentRational.oracleSpec E a 1 (by decide)))
    (LatentRational.value a 1) (coin_lc _) () H hH R

example (E : CoPset) (source : Val rT) (R : IProp GF) :=
  repeated E LatentUniform.model LatentUniform.owns
    (fun x => LatentBernoulli.bias (LatentUniform.model.value x))
    (fun v => pl(&Occil.PSRN.coin &v.fst #()))
    (Coin.coin_programSpec E LatentUniform.model (fun _ => measurable_const)
      LatentUniform.owns (LatentUniform.oracleSpec E))
    source (coin_lc source) [] (fun _ _ _ => ∞)
    (fun _ _ => measurable_const) R

end concrete

private theorem both_true_kernel (u : ℝ) (hu : u ∈ Set.Ico 0 1) :
    LatentCoin.kernel (fun x : ℝ => LatentBernoulli.bias x)
      (fun b => LatentCoin.kernel (fun x : ℝ => LatentBernoulli.bias x)
        (fun c _ => if b && c then 1 else 0)) u = ENNReal.ofReal (u ^ 2) := by
  simp [LatentCoin.kernel, RealCoin.credit, RealCoin.pmf, LatentBernoulli.bias_coe hu,
    pow_two, ENNReal.ofReal_mul hu.1]

/-- Averaging p² over a uniform p gives1/3, retaining the dependence of the two trials. -/
private theorem both_true_moment :
    (∫⁻ u, LatentCoin.kernel (fun x : ℝ => LatentBernoulli.bias x)
      (fun b => LatentCoin.kernel (fun x : ℝ => LatentBernoulli.bias x)
        (fun c _ => if b && c then 1 else 0)) u ∂DyadicPosterior.unitLaw) =
      (1 : ℝ≥0∞) / 3 := by
  have hu : ∀ᵐ u ∂DyadicPosterior.unitLaw, u ∈ Set.Ico (0 : ℝ) 1 := by
    simpa only [DyadicPosterior.law_nil] using DyadicPosterior.ae_mem_unit []
  calc
    _ = ∫⁻ u, ENNReal.ofReal (u ^ 2) ∂DyadicPosterior.unitLaw :=
      MeasureTheory.lintegral_congr_ae (hu.mono fun u hu => both_true_kernel u hu)
    _ = ENNReal.ofReal (∫ u in (0 : ℝ)..1, u ^ 2) := by
      rw [DyadicPosterior.unitLaw, MeasureTheory.restrict_Ico_eq_restrict_Icc,
        ProbLang.TotalEris.Examples.lintegral_ofReal_Icc zero_le_one (by fun_prop)
          (fun u _ => sq_nonneg u)]
    _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]

example : LatentCoin.kernel (fun _ : Unit => LatentBernoulli.bias (-1))
    (fun b _ => if b then ∞ else 0) () = 0 := by
  norm_num [LatentCoin.kernel, LatentBernoulli.bias, RealCoin.credit, RealCoin.pmf,
    Set.projIcc_of_le_left zero_le_one (by norm_num : (-1 : ℝ) ≤ 0)]

example : LatentCoin.kernel (fun _ : Unit => LatentBernoulli.bias 2)
    (fun b _ => if b then 0 else ∞) () = 0 := by
  norm_num [LatentCoin.kernel, LatentBernoulli.bias, RealCoin.credit, RealCoin.pmf,
    Set.projIcc_of_right_le zero_le_one (by norm_num : (1 : ℝ) ≤ 2)]

#print axioms SampLib.LatentReal.Coin.coin_programSpec
#print axioms SampLib.LatentReal.Coin.coin_spec
#print axioms SampLib.LatentReal.UniformThreshold.expectation
#print axioms SampLib.LatentReal.UniformThreshold.ae_distinct
#print axioms repeated
#print axioms both_true_moment

end
end ReviewExactConditionalCoin001
