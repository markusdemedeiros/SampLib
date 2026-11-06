import SampLib.PSRN.Support.PSRNSimplexOutput

/-! # Uniform lazy vectors on the open simplex

`newSimplex n` returns `n` jointly owned coordinate oracles whose vector law is uniform on
the simplex: `output_law_uniform` identifies it as `m!` times Lebesgue measure on the open
region `{y > 0, ∑ y < 1}` of the first `m = n - 1` coordinates, completed by `1 - ∑ y`.
Every dimension shares the unit-rate exponential world: the singleton leaves it unobserved
and returns the constant unit oracle, while larger dimensions normalize the actual
independent exponentials by their common sum.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
/-- The singleton branch keeps the initial world and its whole credit. -/
theorem singleton_payloadSpec (E : CoPset) :
    IsLatentPayloadSpec (GF := GF) E pl(&Occil.PSRN.newSimplex #int ((1 : ℕ) : ℤ) #())
      (world 1) (initial 1) (VectorOwns (outputOwns 1)) := by
  refine ⟨fun F hF => ?_⟩
  iintro Hcredit
  rw [Nat.cast_one]
  iapply tglWp_wand
  isplitl [Hcredit]
  · iapply twp_singleton E _ $$ Hcredit
  iintro %v ⟨%hv, Hcredit⟩
  iexists initial 1
  isplitl []
  · ipureintro
    exact (world 1).refines_refl _
  iframe Hcredit
  isimp only [VectorOwns]
  iexists singletonHandles
  rw [outputOwns_one rfl]
  ipureintro
  exact ⟨hv, fun _ => rfl⟩

/-- Every positive dimension returns the actual handles of one uniform simplex vector. -/
theorem newSimplex_vectorSpec (E : CoPset) (n : ℕ) (hn : 0 < n) :
    IsLatentVectorSpec (GF := GF) E pl(&Occil.PSRN.newSimplex #int (n : ℤ) #())
      (world n) (output n) (initial n) (outputOwns n) where
  sameWorld := output_sameWorld n
  coordinate := output_coordinateSpec E n
  payload := by
    by_cases h1 : n = 1
    · subst n
      exact singleton_payloadSpec E
    · rw [outputOwns_many h1]
      exact many_payloadSpec E n (by omega)

end

end SampLib.PSRNSimplex
