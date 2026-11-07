import SampLib.Latent.LatentUniform
import SampLib.PSRN.Support.Represented.Spec
import SampLib.PSRN.Laws.DyadicInterval

/-! # The actual dyadic representation of a deferred uniform

Each read returns the cell containing the shared latent uniform. Half-open
posterior cells identify its integer rank exactly, including after earlier reads.
The existing constructor and observer supply the program steps unchanged.
-/

open ProbLang
open scoped ENNReal Topology

namespace SampLib.LatentUniform

noncomputable section

section mathematics

open MeasureTheory Set Filter
open LatentReal

/-- The source's returned interval is determined by its latent value and precision. -/
def representation : Representation model where
  interval := dyadicInterval
  measurable_lower n := Int.measurable_floor.comp (by fun_prop)
  measurable_upper n := (Int.measurable_floor.comp (by fun_prop)).add_const 1
  measurable_denominator _ := measurable_const
  approximates _ := Filter.Eventually.of_forall dyadicInterval_approximates

/-- A refined prefix identifies the same half-open cell at every earlier precision. -/
theorem interval_observed {p q : List Bool} {n : ℕ}
    (hread : UniformBag.readRefines p n q) :
    representation.Observed q n (interval q n) := by
  have hn : n ≤ q.length := by rw [hread.2]; exact le_max_right _ _
  have hcell := (DyadicPosterior.law_refines (List.take_prefix n q)).ae_le
    (DyadicPosterior.ae_mem_cell (q.take n))
  filter_upwards [hcell] with x hx
  rw [cell_eq_rank] at hx
  simp only [List.length_take, Nat.min_eq_left hn, mem_Ico] at hx
  have hD : (0 : ℝ) < 2 ^ n := by positivity
  have hrank : ⌊x * 2 ^ n⌋ = UniformBag.rank (q.take n) :=
    Int.floor_eq_iff.mpr ⟨(div_le_iff₀ hD).mp hx.1, (lt_div_iff₀ hD).mp hx.2⟩
  change interval q n = dyadicInterval n x
  simp only [interval, dyadicInterval, hrank]

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Strengthen the original observer without replaying its program proof. -/
theorem representedOracleSpec (E : CoPset) :
    LatentReal.IsRepresentedOracleSpec (GF := GF) E model representation owns where
  observe v p n F hF := by
    iintro Hstate
    have hread := twp_observe (rT := rT) (GF := GF) E v p n F hF
    unfold DyadicPosterior.credit at hread
    isimp only [model] at Hstate
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply hread $$ Hstate
    iintro %result ⟨%q, %hq, Hstate, Hcredit⟩
    rcases hq with ⟨hrefines, rfl⟩
    iexists q, interval q n
    rw [show model.posterior q = DyadicPosterior.law q from rfl]
    iframe Hstate Hcredit
    ipureintro
    exact ⟨rfl, hrefines.1, interval_encloses hrefines, interval_observed hrefines⟩

/-- Construction and every observation retain the original uniform and its cached digits. -/
theorem newUniform_representedDistSpec (E : CoPset) :
    LatentReal.IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newUniform #())
      model representation [] owns where
  spec := (newUniform_latentDistSpec E).spec
  oracle := representedOracleSpec E

end specification

end

end SampLib.LatentUniform
