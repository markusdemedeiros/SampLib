import SampLib.Latent.LatentUniform
import SampLib.PSRN.PSRNRejection

open ProbLang
open scoped ENNReal

namespace ReviewExactLatent002

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def halfCell : Set ℝ := Set.Iio (1 / 2)

local instance : DecidablePred (· ∈ halfCell) := fun _ => Classical.propDecidable _

private def acceptHalf : Val rT :=
  ⟨.lam (.binop .eq (.fst (.app (.bvar 0) (.lit (.int 1)))) (.lit (.int 0))),
    .lam (by is_lc), by is_lc⟩

private theorem first_bit_resolves (bit : Bool) (tail : List Bool) :
    DyadicPosterior.resolves (bit :: tail) (1 / 2) (!bit) := by
  rw [DyadicPosterior.resolves_cons]
  cases bit
  · exact DyadicPosterior.resolves_true tail (by norm_num)
  · exact DyadicPosterior.resolves_false tail (by norm_num)

/-- This callback reads the proposed uniform's own cached first bit. -/
private theorem acceptHalf_spec (E : CoPset) :
    LatentReal.IsEventSpec (GF := GF) E LatentUniform.model LatentUniform.owns
      halfCell acceptHalf where
  measurable_event := measurableSet_Iio
  spec source p G hG := by
    let F : ℝ → ℝ≥0∞ := fun u => G (decide (u ∈ halfCell)) u
    have hF : Measurable F := by
      have heq : F = fun u => if u < (1 / 2 : ℝ) then G true u else G false u := by
        funext u
        change G (decide (u < (1 / 2 : ℝ))) u = _
        by_cases hu : u < (1 / 2 : ℝ)
        · rw [ite_eq_left hu, decide_eq_true hu]
        · rw [ite_eq_right hu, decide_eq_false hu]
      rw [heq]
      exact Measurable.ite measurableSet_Iio (hG true) (hG false)
    iintro ⟨Hstate, Hcredit⟩
    isimp only [LatentUniform.model] at Hcredit
    twp_pure
    twp_bind pl(&source.fst #1)
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply LatentUniform.twp_observe E source p 1 F hF
      isimp only [DyadicPosterior.credit, F]
      iframe Hstate Hcredit
    iintro %result ⟨%q, %hq, Hstate, Hcredit⟩
    rcases hq with ⟨hrefines, rfl⟩
    cases q with
    | nil =>
      have hlength := hrefines.2
      simp only [List.length_nil] at hlength
      omega
    | cons bit tail =>
      have hres := first_bit_resolves bit tail
      have hcredit : DyadicPosterior.credit (bit :: tail) F =
          DyadicPosterior.credit (bit :: tail) (G (!bit)) := by
        apply MeasureTheory.lintegral_congr_ae
        exact hres.mono fun u hu => by simp only [F, halfCell, Set.mem_Iio, hu]
      isimp only [hcredit] at Hcredit
      cases bit <;> simp only [LatentUniform.interval, LatentReal.intervalVal,
        List.take_succ_cons, List.take_zero, UniformBag.rank,
        List.length_nil, pow_zero, Bool.false_eq_true, ite_false, ite_true,
        zero_mul, one_mul, add_zero]
      all_goals
        twp_pures
        twp_value
        imodintro
        iexists _, _
        isimp only [LatentUniform.model, DyadicPosterior.credit] at Hcredit
        isimp only [LatentUniform.model, DyadicPosterior.credit]
        iframe Hstate Hcredit
        ipureintro
        exact ⟨rfl, hrefines.1, hres⟩

private def proposal : Val rT :=
  ⟨.lam (.app Occil.PSRN.newUniform (.lit .unit)), .lam (by is_lc), by is_lc⟩

private theorem proposal_spec (E : CoPset) :
    LatentReal.IsLatentDistSpec (GF := GF) E pl(&(proposal : Val rT).fst #())
      LatentUniform.model [] LatentUniform.owns where
  oracle := LatentUniform.oracleSpec E
  spec F hF := by
    iintro Hcredit
    twp_pure
    rw [← Exp.open_lc 0 pl(#()) Occil.PSRN.newUniform (by is_lc)]
    iapply (LatentUniform.newUniform_latentDistSpec E).spec F hF $$ Hcredit

private theorem half_mass : LatentUniform.model.posterior [] halfCell = (2 : ℝ≥0∞)⁻¹ := by
  change DyadicPosterior.law [] (Set.Iio (1 / 2 : ℝ)) = _
  rw [DyadicPosterior.law_nil, DyadicPosterior.unitLaw,
    MeasureTheory.Measure.restrict_apply measurableSet_Iio, Set.inter_comm,
    Set.Ico_inter_Iio]
  norm_num [ENNReal.ofReal_div_of_pos]

private theorem half_mass_ne_zero : LatentUniform.model.posterior [] halfCell ≠ 0 := by
  rw [half_mass]
  exact ENNReal.inv_ne_zero.mpr (by simp)

/-- A genuinely rejecting callback retains a uniform conditioned on its own first bit. -/
private theorem half_rejection (E : CoPset) :
    LatentReal.IsLatentDistSpec (GF := GF) E
      pl(&Occil.PSRN.newRejection &(proposal : Val rT).fst &(acceptHalf : Val rT).fst #())
      (LatentReal.Conditioning.model LatentUniform.model [] halfCell half_mass_ne_zero)
      none (LatentReal.Conditioning.owns LatentUniform.model [] halfCell LatentUniform.owns) :=
  PSRNRejection.newRejection_latentDistSpec E LatentUniform.model [] LatentUniform.owns
    halfCell half_mass_ne_zero proposal acceptHalf (proposal_spec E) (acceptHalf_spec E)

private def observeAfter (e : Exp rT) (n : ℕ) : Exp rT :=
  .app (.lam (.app (.bvar 0) (.lit (.int n)))) e

omit [ProbLangDist.IsUniformInt rT] in
/-- Construction, the accepted oracle and a later read retain one conditional latent law. -/
theorem construct_read {Ω S : Type} [MeasurableSpace Ω] (E : CoPset)
    (D : LatentReal.Model Ω S) (initial : S) (owns : Val rT → S → IProp GF)
    (e : Exp rT) (h : LatentReal.IsLatentDistSpec E e D initial owns) (n : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂D.posterior initial) ∗ R -∗ tglWp E (observeAfter e n)
      (fun result : Val rT => iprop(∃ (v : Val rT) (t : S) (I : LatentReal.RationalInterval),
        ⌜result = LatentReal.intervalVal I ∧ D.refines initial t ∧ D.Encloses t n I⌝ ∗
        owns v t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  unfold observeAfter
  twp_bind e
  iapply (h.wp F hF _) $$ Hcredit
  iintro %v %s %hs Hstate Hcredit
  twp_pure
  iapply (h.oracle.wp v s n F hF _) $$ Hstate Hcredit
  iintro %t %I %ht Hstate Hcredit
  iexists v, t, I
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, D.refines_trans hs ht.1, ht.2⟩

example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_read E
    (LatentReal.Conditioning.model LatentUniform.model [] halfCell half_mass_ne_zero)
    none (LatentReal.Conditioning.owns LatentUniform.model [] halfCell LatentUniform.owns)
    pl(&Occil.PSRN.newRejection &(proposal : Val rT).fst &(acceptHalf : Val rT).fst #())
    (half_rejection E) 3 F hF R

example (E : CoPset) (R : IProp GF) :=
  construct_read E
    (LatentReal.Conditioning.model LatentUniform.model [] halfCell half_mass_ne_zero)
    none (LatentReal.Conditioning.owns LatentUniform.model [] halfCell LatentUniform.owns)
    pl(&Occil.PSRN.newRejection &(proposal : Val rT).fst &(acceptHalf : Val rT).fst #())
    (half_rejection E) 0 (fun _ => ∞) measurable_const R

#print axioms acceptHalf_spec
#print axioms half_rejection
#print axioms half_mass
#print axioms construct_read
#print axioms SampLib.PSRNRejection.newRejection_latentDistSpec
#print axioms SampLib.LatentRejectionKernel.twp_newRejection

end

end ReviewExactLatent002
