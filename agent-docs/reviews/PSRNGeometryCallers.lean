import SampLib.PSRN.PSRNSimplex
import SampLib.PSRN.PSRNOddsUniform
import SampLib.PSRN.PSRNRatioUniforms
import SampLib.PSRN.PSRNReciprocalPowerUniform

/-! Owner-side callers for the PSRN geometry team (not a review receipt). -/

open ProbLang
open scoped ENNReal Nat

namespace PSRNGeometryCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Read one coordinate at precision 4 and then an alias of it at precision 2. -/
private def readTwice (handle : Val rT) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) (.app handle.fst (.lit (.int 2)))))
    (.app handle.fst (.lit (.int 4)))

omit [ProbLangDist.IsUniformInt rT] in
theorem alias_reads {Ω S : Type} [MeasurableSpace Ω] (E : CoPset)
    (D V : Model Ω S) (P : S → IProp GF) (hw : D.SameWorld V) (handle : Val rT)
    (hc : IsViewSpec E V P handle) (s : S) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :
    ⊢ P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R -∗
      tglWp E (readTwice handle) (fun result : Val rT =>
        iprop(∃ (t : S) (I J : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧ D.refines s t ∧
            V.Encloses t 4 I ∧ V.Encloses t 2 J⌝ ∗
          P t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readTwice
  twp_bind pl(&handle.fst #4)
  isimp only [← hw.posterior_eq s] at Hcredit
  iapply hc.wp s 4 F hF _ $$ Hstate Hcredit
  iintro %t %I %⟨hst, hI⟩ Hstate Hcredit
  twp_pure
  twp_bind pl(&handle.fst #2)
  iapply hc.wp t 2 F hF _ $$ Hstate Hcredit
  iintro %u %J %⟨htu, hJ⟩ Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  isimp only [hw.posterior_eq u] at Hcredit
  iexists u, I, J
  iframe Hstate Hcredit HR
  ipureintro
  exact ⟨rfl, (hw.refines_iff s u).mp (V.refines_trans hst htu), V.encloses_refines htu hI, hJ⟩

/-- Construct a simplex of any positive dimension under a frame, then read an aliased
coordinate; the joint credit stays on the one exponential world throughout. -/
theorem construct_and_read (E : CoPset) (n : ℕ) (hn : 0 < n) (i : Fin n)
    (F : PSRNSimplex.World n → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂(PSRNSimplex.world n).posterior (PSRNSimplex.initial n)) ∗ R -∗
      tglWp E pl(&Occil.PSRN.newSimplex #int (n : ℤ) #())
        (fun v : Val rT => iprop(∃ handles t,
          ⌜v = vectorVal handles ∧ (PSRNSimplex.world n).refines (PSRNSimplex.initial n) t⌝ ∗
          tglWp E (readTwice (handles i)) (fun result : Val rT =>
            iprop(∃ (u : PSRNSimplex.State n) (I J : RationalInterval),
              ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧
                (PSRNSimplex.world n).refines t u ∧
                (PSRNSimplex.output n i).Encloses u 4 I ∧
                (PSRNSimplex.output n i).Encloses u 2 J⌝ ∗
              PSRNSimplex.outputOwns n handles u ∗
              ↯ (∫⁻ x, F x ∂(PSRNSimplex.world n).posterior u) ∗ R)))) := by
  have h := PSRNSimplex.newSimplex_vectorSpec (rT := rT) (GF := GF) E n hn
  iintro ⟨Hcredit, HR⟩
  iapply h.wp F hF _ $$ Hcredit
  iintro %handles %t %ht Hstate Hcredit
  iexists handles, t
  isplitl []
  · ipureintro
    exact ⟨rfl, ht⟩
  iapply alias_reads E _ _ _ (h.sameWorld i) (handles i) (h.coordinate handles i) t F hF R
  iframe Hstate Hcredit HR

/-- Infinite credit and both regimes of the source guard: the singleton and n = 2. -/
example (E : CoPset) (R : IProp GF) :=
  construct_and_read (rT := rT) E 1 one_pos 0 (fun _ => ∞) measurable_const R

example (E : CoPset) (F : PSRNSimplex.World 2 → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_read (rT := rT) E 2 two_pos 1 F hF R

/-- The identified joint law is canonical: `m!` Lebesgue on the open simplex region,
completed by the last coordinate, in every positive dimension `m + 1`. -/
example (m : ℕ) : vectorLaw (PSRNSimplex.world (m + 1)) (PSRNSimplex.output (m + 1))
    (PSRNSimplex.initial (m + 1)) = (UniformSimplex.law m).map UniformSimplex.embed :=
  PSRNSimplex.output_law_uniform m

example (m : ℕ) : (vectorLaw (PSRNSimplex.world (m + 1)) (PSRNSimplex.output (m + 1))
    (PSRNSimplex.initial (m + 1))).map (fun x i => x (Fin.castSucc i)) =
      ((m ! : ℕ) : ℝ≥0∞) • MeasureTheory.volume.restrict
        {y : Fin m → ℝ | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} :=
  PSRNSimplex.output_firstCoordinates m

omit [ProbLangDist.IsUniformInt rT] in
/-- Construct any scalar latent draw under a frame, then read the returned oracle twice. -/
theorem scalar_construct_and_read {Ω S : Type} [MeasurableSpace Ω] (E : CoPset) (e : Exp rT)
    (D : Model Ω S) (initial : S) (owns : Val rT → S → IProp GF)
    (h : IsLatentDistSpec E e D initial owns) (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂D.posterior initial) ∗ R -∗
      tglWp E e (fun v : Val rT => iprop(∃ t, ⌜D.refines initial t⌝ ∗
        tglWp E (readTwice v) (fun result : Val rT =>
          iprop(∃ (u : S) (I J : RationalInterval),
            ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧ D.refines t u ∧
              D.Encloses u 4 I ∧ D.Encloses u 2 J⌝ ∗
            owns v u ∗ ↯ (∫⁻ x, F x ∂D.posterior u) ∗ R)))) := by
  iintro ⟨Hcredit, HR⟩
  iapply h.wp F hF _ $$ Hcredit
  iintro %v %t %ht Hstate Hcredit
  iexists t
  isplitl []
  · ipureintro
    exact ht
  iapply alias_reads E D D (owns v) (Model.SameWorld.refl D) v (h.oracle.viewSpec E D owns v)
    t F hF R
  iframe Hstate Hcredit HR

example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNOddsUniform.newOddsUniform_latentDistSpec (rT := rT) (GF := GF) E) F hF R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNOddsUniform.newOddsUniform_latentDistSpec (rT := rT) (GF := GF) E)
    (fun _ => ∞) measurable_const R

example (E : CoPset) (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNRatioUniforms.newRatioUniforms_latentDistSpec (rT := rT) (GF := GF) E) F hF R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNRatioUniforms.newRatioUniforms_latentDistSpec (rT := rT) (GF := GF) E)
    (fun _ => ∞) measurable_const R

/-- The identified laws: uniform odds and the quotient of two independent uniforms. -/
example : PSRNOddsUniform.model.law [] =
    (ProbabilityTheory.paretoMeasure 1 1).map (fun x : ℝ => x - 1) :=
  PSRNOddsUniform.initial_law.trans UniformOdds.law_eq_shifted_pareto

example : PSRNRatioUniforms.model.law PSRNRatioUniforms.initial =
    (DyadicPosterior.unitLaw.prod DyadicPosterior.unitLaw).map (fun z : ℝ × ℝ => z.1 / z.2) :=
  PSRNRatioUniforms.initial_law

/-- Every exponent regime of the actual source: zero, positive and negative numerators,
each with degree-one and bisection roots. -/
example (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNPowerUniform.newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E a b hb) F hF R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNPowerUniform.newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 0 1 one_pos)
    (fun _ => ∞) measurable_const R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNPowerUniform.newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 3 1 one_pos)
    (fun _ => ∞) measurable_const R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNPowerUniform.newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E 1 2 two_pos)
    (fun _ => ∞) measurable_const R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNPowerUniform.newPowerUniform_latentDistSpec (rT := rT) (GF := GF) E (-2) 3
      (by norm_num)) (fun _ => ∞) measurable_const R

example (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec (rT := rT) (GF := GF)
      E a b hb) F hF R

example (E : CoPset) (R : IProp GF) :=
  scalar_construct_and_read E _ _ _ _
    (PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec (rT := rT) (GF := GF)
      E (-1) 1 one_pos) (fun _ => ∞) measurable_const R

/-- The identified laws: `u ^ (a / b)` and `u ^ (-a / b)` for a unit uniform `u`. -/
example (a : ℤ) (b : ℕ) (hb : 0 < b) : (PSRNPowerUniform.model a b).law [] =
    DyadicPosterior.unitLaw.map (fun u => u ^ ((a : ℝ) / b)) :=
  PSRNPowerUniform.initial_law a hb

example (a : ℤ) (b : ℕ) (hb : 0 < b) : (PSRNReciprocalPowerUniform.model a b).law [] =
    DyadicPosterior.unitLaw.map (fun u => u ^ (-(a : ℝ) / b)) :=
  PSRNReciprocalPowerUniform.initial_law a hb

#print axioms SampLib.PSRNPowerUniform.newPowerUniform_latentDistSpec
#print axioms SampLib.PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec
#print axioms scalar_construct_and_read
#print axioms SampLib.PSRNOddsUniform.newOddsUniform_latentDistSpec
#print axioms SampLib.PSRNRatioUniforms.newRatioUniforms_latentDistSpec
#print axioms alias_reads
#print axioms construct_and_read
#print axioms SampLib.PSRNSimplex.newSimplex_vectorSpec
#print axioms SampLib.PSRNSimplex.output_law
#print axioms SampLib.PSRNSimplex.output_law_uniform
#print axioms SampLib.PSRNSimplex.output_firstCoordinates

end

end PSRNGeometryCallers
