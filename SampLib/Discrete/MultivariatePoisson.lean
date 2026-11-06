import SampLib.Discrete.PoissonRational
import SampLib.Core.ListEncoding
import Samplers.Discrete.Compound

/-! # Shared-component multivariate Poisson counts -/

open ProbLang
open scoped ENNReal NNReal

namespace SampLib.MultivariatePoisson

noncomputable section

/-- A nonnegative rational rate with its denominator certificate. -/
abbrev Rate := {p : ℕ × ℕ // 0 < p.2}

section mathematics

open MeasureTheory Measure

/-- Independent component counts, each shifted by the common count. -/
def components (shared : ℕ) : List Rate → Measure (List ℕ)
  | [] => dirac []
  | r :: rs => ((ProbabilityTheory.poissonMeasure
      (PoissonRational.rate r.val.1 r.val.2)).prod (components shared rs)).map
      (fun p => (shared + p.1) :: p.2)

instance (shared : ℕ) (rs : List Rate) : IsProbabilityMeasure (components shared rs) := by
  induction rs with
  | nil => dsimp [components]; infer_instance
  | cons r rs IH =>
    let := IH
    constructor
    rw [components, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp

/-- A single common Poisson component creates the dependence between coordinates. -/
def law (sharedRate : ℝ≥0) (rs : List Rate) : Measure (List ℕ) :=
  (ProbabilityTheory.poissonMeasure sharedRate).bind (fun shared => components shared rs)

instance (sharedRate : ℝ≥0) (rs : List Rate) : IsProbabilityMeasure (law sharedRate rs) where
  measure_univ := by
    rw [law, Measure.bind_apply MeasurableSet.univ
      (measurable_of_countable _).aemeasurable]
    simp

/-- Condition first on the common count, then on the independent coordinates. -/
theorem expectation (sharedRate : ℝ≥0) (rs : List Rate) (F : List ℕ → ℝ≥0∞) :
    (∫⁻ shared, ∫⁻ ns, F ns ∂components shared rs
      ∂ProbabilityTheory.poissonMeasure sharedRate) = ∫⁻ ns, F ns ∂law sharedRate rs := by
  rw [law, Measure.lintegral_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]

theorem component_expectation (shared : ℕ) (r : Rate) (rs : List Rate)
    (F : List ℕ → ℝ≥0∞) :
    (∫⁻ n, ∫⁻ ns, F ((shared + n) :: ns) ∂components shared rs
      ∂ProbabilityTheory.poissonMeasure (PoissonRational.rate r.val.1 r.val.2)) =
      ∫⁻ ns, F ns ∂components shared (r :: rs) := by
  rw [components, lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_prod _ (measurable_of_countable _).aemeasurable]

end mathematics

def encodeRate {rT : Type _} (r : Rate) : Val rT :=
  Val.pair (Val.int (r.val.1 : ℤ)) (Val.int (r.val.2 : ℤ))

private def loop {rT : Type _} [ProbLangℝ rT] (shared : ℕ) : Exp rT :=
  .fix (.lam (.case (.bvar 0) (.lam pl(inl(#())))
    (.lam (.app (.lam
      (.app (.lam (pl% inr((#int (shared : ℤ) + {Exp.bvar 0},
        {Exp.bvar 4} (snd({Exp.bvar 2}))))))
        (pl% &Occil.poissonRational (fst({Exp.bvar 0})) (snd({Exp.bvar 0})))))
      (.fst (.bvar 0))))))

private theorem encode_cons {rT : Type _} [ProbLangℝ rT] (n : ℕ) (ns : List ℕ) :
    pl(inr((#int (n : ℤ), {Exp.ofVal (listVal (fun n : ℕ => Val.int (n : ℤ)) ns)}))) =
      Exp.ofVal (listVal (fun n : ℕ => Val.int (n : ℤ)) (n :: ns) : Val rT) := by
  simp [Exp.ofVal, listVal]

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem twp_loop (E : CoPset) (shared : ℕ) (rs : List Rate)
    (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ns, F ns ∂components shared rs) -∗
      tglWp E pl(&(loop shared) &(listVal encodeRate rs).fst)
        (fun v : Val rT => iprop(∃ ns : List ℕ,
          ⌜v = listVal (fun n : ℕ => Val.int (n : ℤ)) ns⌝ ∗ ↯ (F ns))) := by
  induction rs generalizing F with
  | nil =>
    iintro Hcredit
    simp only [listVal]
    twp_pures
    twp_value
    imodintro
    iexists []
    isimp only [components, MeasureTheory.lintegral_dirac] at Hcredit
    iframe Hcredit
    ipureintro
    exact Val.ext rfl
  | cons r rs IH =>
    iintro Hcredit
    simp only [listVal, encodeRate]
    iterate 8 twp_pure
    simp only [PoissonRational.poissonRational_openRec]
    twp_bind pl(&Occil.poissonRational #int (r.val.1 : ℤ) #int (r.val.2 : ℤ))
    isimp only [← component_expectation shared r rs F] at Hcredit
    iapply ((PoissonRational.poissonRational_distSpec E r.val.1 r.val.2 r.property).wp
      (fun n => ∫⁻ ns, F ((shared + n) :: ns) ∂components shared rs)
      (measurable_of_countable _) _) $$ Hcredit
    iintro %n Hcredit
    iterate 2 twp_pure
    simp only [PoissonRational.poissonRational_openRec]
    twp_bind pl(&(loop shared) &(listVal encodeRate rs).fst)
    iapply tglWp_wand
    isplitl [Hcredit]
    · iapply IH (fun ns => F ((shared + n) :: ns)) $$ Hcredit
    iintro %v ⟨%ns, %hv, Hcredit⟩
    subst v
    twp_pures
    rw [← Nat.cast_add, encode_cons]
    iapply (tglWp_value (v := listVal (fun n : ℕ => Val.int (n : ℤ))
      ((shared + n) :: ns)))
    iexists (shared + n) :: ns
    iframe Hcredit
    itrivial

theorem twp_multivariatePoisson (E : CoPset) (x y : ℕ) (hy : 0 < y)
    (rs : List Rate) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ ns, F ns ∂law (PoissonRational.rate x y) rs) -∗
      tglWp E pl(&Occil.DiscreteExtra.multivariatePoisson
        #int (x : ℤ) #int (y : ℤ) &(listVal encodeRate rs).fst)
        (fun v : Val rT => iprop(∃ ns : List ℕ,
          ⌜v = listVal (fun n : ℕ => Val.int (n : ℤ)) ns⌝ ∗ ↯ (F ns))) := by
  iintro Hcredit
  iterate 3 twp_pure
  simp only [PoissonRational.poissonRational_openRec,
    PoissonRational.poissonRational_closeRec]
  twp_bind pl(&Occil.poissonRational #int (x : ℤ) #int (y : ℤ))
  isimp only [← expectation (PoissonRational.rate x y) rs F] at Hcredit
  iapply ((PoissonRational.poissonRational_distSpec E x y hy).wp
    (fun shared => ∫⁻ ns, F ns ∂components shared rs)
    (measurable_of_countable _) _) $$ Hcredit
  iintro %shared Hcredit
  iterate 2 twp_pure
  simp only [PoissonRational.poissonRational_openRec]
  have h := twp_loop (rT := rT) (GF := GF) E shared rs F
  simp [loop] at h
  iapply h $$ Hcredit

theorem multivariatePoisson_distSpec (E : CoPset) (x y : ℕ) (hy : 0 < y)
    (rs : List Rate) :
    IsDistSpec (GF := GF) E pl(&Occil.DiscreteExtra.multivariatePoisson
      #int (x : ℤ) #int (y : ℤ) &(listVal encodeRate rs).fst)
      (law (PoissonRational.rate x y) rs)
      (listVal (fun n : ℕ => Val.int (n : ℤ))) where
  spec F _ := wand_entails (twp_multivariatePoisson E x y hy rs F)

end specification

end

end SampLib.MultivariatePoisson
