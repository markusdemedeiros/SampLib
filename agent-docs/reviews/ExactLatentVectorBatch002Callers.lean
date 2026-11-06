import SampLib.Samplers.PSRNSimplex

open ProbLang
open scoped ENNReal

namespace ReviewExactLatentVector002

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Read handle `x` at precision `p`, then handle `y` at precision `q`. -/
private def readPair (x y : Val rT) (p q : ℕ) : Exp rT :=
  .app (.lam (.app (.lam (.pair (.bvar 1) (.bvar 0))) (.app y.fst (.lit (.int q)))))
    (.app x.fst (.lit (.int p)))

omit [ProbLangDist.IsUniformInt rT] in
/-- Two coordinate views of one world read in sequence; joint credit stays on the world. -/
theorem read_pair {Ω S : Type} [MeasurableSpace Ω] (E : CoPset) (D V W : Model Ω S)
    (P : S → IProp GF) (hV : D.SameWorld V) (hW : D.SameWorld W) (x y : Val rT)
    (hx : IsViewSpec E V P x) (hy : IsViewSpec E W P y) (s : S) (p q : ℕ)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ P s ∗ ↯ (∫⁻ ω, F ω ∂D.posterior s) ∗ R -∗
      tglWp E (readPair x y p q) (fun result : Val rT =>
        iprop(∃ (u : S) (I J : RationalInterval),
          ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧ D.refines s u ∧
            V.Encloses u p I ∧ W.Encloses u q J⌝ ∗
          P u ∗ ↯ (∫⁻ ω, F ω ∂D.posterior u) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readPair
  twp_bind pl(&x.fst #int (p : ℤ))
  isimp only [← hV.posterior_eq s] at Hcredit
  iapply hx.wp s p F hF _ $$ Hstate Hcredit
  iintro %t %I %⟨hst, hI⟩ Hstate Hcredit
  twp_pure
  twp_bind pl(&y.fst #int (q : ℤ))
  isimp only [hV.posterior_eq t, ← hW.posterior_eq t] at Hcredit
  iapply hy.wp t q F hF _ $$ Hstate Hcredit
  iintro %u %J %⟨htu, hJ⟩ Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  isimp only [hW.posterior_eq u] at Hcredit
  iexists u, I, J
  iframe Hstate Hcredit HR
  ipureintro
  have htu' := (hW.refines_iff t u).mp htu
  exact ⟨rfl, D.refines_trans ((hV.refines_iff s t).mp hst) htu',
    V.encloses_refines ((hV.refines_iff t u).mpr htu') hI, hJ⟩

/-- Build a simplex under a frame, then read coordinates `i` and `j` (possibly equal). -/
theorem construct_and_read (E : CoPset) (n : ℕ) (hn : 0 < n) (i j : Fin n) (p q : ℕ)
    (F : PSRNSimplex.World n → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂(PSRNSimplex.world n).posterior (PSRNSimplex.initial n)) ∗ R -∗
      tglWp E pl(&Occil.PSRN.newSimplex #int (n : ℤ) #())
        (fun v : Val rT => iprop(∃ handles t,
          ⌜v = vectorVal handles ∧ (PSRNSimplex.world n).refines (PSRNSimplex.initial n) t⌝ ∗
          tglWp E (readPair (handles i) (handles j) p q) (fun result : Val rT =>
            iprop(∃ (u : PSRNSimplex.State n) (I J : RationalInterval),
              ⌜result = Val.pair (intervalVal I) (intervalVal J) ∧
                (PSRNSimplex.world n).refines t u ∧
                (PSRNSimplex.output n i).Encloses u p I ∧
                (PSRNSimplex.output n j).Encloses u q J⌝ ∗
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
  iapply read_pair E _ _ _ _ (h.sameWorld i) (h.sameWorld j) (handles i) (handles j)
    (h.coordinate handles i) (h.coordinate handles j) t p q F hF R
  iframe Hstate Hcredit HR

-- Singleton boundary: constant unit oracle, infinite credit, alias read at precision zero.
example (E : CoPset) (R : IProp GF) :=
  construct_and_read (rT := rT) E 1 one_pos 0 0 0 5 (fun _ => ∞) measurable_const R

-- Smallest normalizing dimension, distinct coordinates, arbitrary joint credit.
example (E : CoPset) (F : PSRNSimplex.World 2 → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_read (rT := rT) E 2 two_pos 0 1 6 2 F hF R

example (E : CoPset) (R : IProp GF) :=
  construct_and_read (rT := rT) E 3 (by decide) 2 2 0 9 (fun _ => ∞) measurable_const R

example (E : CoPset) (n : ℕ) (hn : 0 < n) (i j : Fin n)
    (F : PSRNSimplex.World n → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  construct_and_read (rT := rT) E n hn i j 4 7 F hF R

section laws

open MeasureTheory

/-- The canonical law on the spec's own world/output/initial state, in every dimension. -/
example (m : ℕ) :
    vectorLaw (PSRNSimplex.world (m + 1)) (PSRNSimplex.output (m + 1))
      (PSRNSimplex.initial (m + 1)) = (UniformSimplex.law m).map UniformSimplex.embed :=
  PSRNSimplex.output_law_uniform m

/-- Reviewer check: for `n = 3` the first two coordinates have density `2` on the triangle. -/
theorem triangle_density :
    (vectorLaw (PSRNSimplex.world 3) (PSRNSimplex.output 3) (PSRNSimplex.initial 3)).map
      (fun x i => x (Fin.castSucc i)) =
      (2 : ℝ≥0∞) • volume.restrict {y : Fin 2 → ℝ | (∀ i, 0 < y i) ∧ y 0 + y 1 < 1} := by
  rw [PSRNSimplex.output_firstCoordinates 2, UniformSimplex.law, UniformSimplex.region]
  simp [Fin.sum_univ_two, Nat.factorial]

/-- Reviewer check: the singleton output is the point mass at `(1)`. -/
theorem singleton_law :
    vectorLaw (PSRNSimplex.world 1) (PSRNSimplex.output 1) (PSRNSimplex.initial 1) =
      Measure.dirac (fun _ => 1) := by
  rw [PSRNSimplex.output_law_uniform 0, UniformSimplex.law, UniformSimplex.region]
  have hset : {y : Fin 0 → ℝ | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} = Set.univ := by
    ext y
    simp
  rw [hset, Measure.restrict_univ, volume_pi, Measure.pi_of_empty,
    Nat.factorial_zero, Nat.cast_one, one_smul]
  refine (Measure.map_dirac' (UniformSimplex.measurable_embed 0) _).trans ?_
  congr 1
  funext i
  simp [UniformSimplex.embed, Fin.snoc, Fin.fin_one_eq_zero i]

end laws

#print axioms SampLib.PSRNSimplex.newSimplex_vectorSpec
#print axioms SampLib.PSRNSimplex.output_law_uniform
#print axioms SampLib.PSRNSimplex.output_firstCoordinates
#print axioms SampLib.UniformSimplex.simplex_eq
#print axioms construct_and_read
#print axioms triangle_density
#print axioms singleton_law

end

end ReviewExactLatentVector002
