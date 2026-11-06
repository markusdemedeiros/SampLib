import SampLib.PSRN.PSRNInsideShape

open ProbLang
open scoped ENNReal

namespace ReviewExactLatentVector001

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private def halfSpace : Set (Fin 2 → ℝ) := {x | x 0 < 1 / 2}
local instance : DecidablePred (· ∈ halfSpace) := fun _ => Classical.propDecidable _

private def acceptHalf : Val rT :=
  ⟨.lam (.binop .eq (.fst (.app
    (.app (.app Occil.getAt (.bvar 0)) (.lit (.int 0))) (.lit (.int 1)))) (.lit (.int 0))),
    .lam (by is_lc), by is_lc⟩

private theorem first_bit_resolves (bit : Bool) (tail : List Bool) :
    DyadicPosterior.resolves (bit :: tail) (1 / 2) (!bit) := by
  rw [DyadicPosterior.resolves_cons]
  cases bit
  · exact DyadicPosterior.resolves_true tail (by norm_num)
  · exact DyadicPosterior.resolves_false tail (by norm_num)

private theorem acceptHalf_spec (E : CoPset) :
    IsEventSpec (GF := GF) E (UniformVector.world 2) (VectorOwns UniformVector.owns)
      halfSpace acceptHalf where
  measurable_event := measurableSet_lt (measurable_pi_apply 0) measurable_const
  spec source p G hG := by
    let F : (Fin 2 → ℝ) → ℝ≥0∞ := fun u => G (decide (u ∈ halfSpace)) u
    have hF : Measurable F := by
      have heq : F = fun u => if u 0 < (1 / 2 : ℝ) then G true u else G false u := by
        funext u
        change G (decide (u 0 < (1 / 2 : ℝ))) u = _
        by_cases hu : u 0 < (1 / 2 : ℝ)
        · rw [ite_eq_left hu, decide_eq_true hu]
        · rw [ite_eq_right hu, decide_eq_false hu]
      rw [heq]
      exact Measurable.ite (measurableSet_lt (measurable_pi_apply 0) measurable_const)
        (hG true) (hG false)
    iintro ⟨Hstate, Hcredit⟩
    isimp only [VectorOwns, UniformVector.owns] at Hstate
    ihave ⟨%handles, %hv, %roots, %hhandles, Hroots⟩ := Hstate
    subst source handles
    twp_pure
    twp_bind pl(&Occil.getAt &(vectorVal (fun i => LatentUniform.value (roots i))).fst #0)
    iapply (tglWp_wand (Φ := fun v : Val rT =>
      iprop(⌜v = LatentUniform.value (roots 0)⌝)))
    isplitl []
    · simp only [vectorVal, List.ofFn_succ, List.ofFn_zero, listVal]
      twp_pures
      twp_value
      imodintro
      ipureintro
      rfl
    iintro %handle %hhandle
    subst handle
    twp_bind pl(&(LatentUniform.value (rT := rT) (roots 0)).fst #1)
    iapply tglWp_wand
    isplitl [Hroots Hcredit]
    · iapply UniformVector.twp_observe_coordinate E roots p 0 1 F hF
      isimp only [UniformVector.world] at Hcredit
      isimp only [F]
      iframe Hroots Hcredit
    iintro %result ⟨%q, %hq, Hroots, Hcredit⟩
    rcases hq with ⟨hrefines, rfl⟩
    cases q with
    | nil =>
      have hlength := hrefines.2
      simp only [List.length_nil] at hlength
      omega
    | cons bit tail =>
      have hres : ∀ᵐ x ∂UniformVector.law (Function.update p 0 (bit :: tail)),
          decide (x ∈ halfSpace) = !bit := by
        change ∀ᵐ x ∂UniformVector.law (Function.update p 0 (bit :: tail)),
          decide (x 0 < (1 / 2 : ℝ)) = !bit
        apply UniformVector.ae_coordinate _ 0
          (P := fun x => decide (x < (1 / 2 : ℝ)) = !bit)
        simpa only [Function.update_self, DyadicPosterior.resolves] using first_bit_resolves bit tail
      have hcredit : (∫⁻ x, F x ∂UniformVector.law (Function.update p 0 (bit :: tail))) =
          ∫⁻ x, G (!bit) x ∂UniformVector.law (Function.update p 0 (bit :: tail)) :=
        MeasureTheory.lintegral_congr_ae (hres.mono fun _ hu => by simp only [F, hu])
      isimp only [hcredit] at Hcredit
      cases bit <;> simp only [LatentUniform.interval, intervalVal,
        List.take_succ_cons, List.take_zero, UniformBag.rank,
        List.length_nil, pow_zero, Bool.false_eq_true, ite_false, ite_true,
        zero_mul, one_mul, add_zero]
      all_goals
        twp_pures
        twp_value
        imodintro
        iexists _, _
        isplitl []
        · ipureintro
          exact ⟨rfl, UniformVector.refines_update p 0 _ hrefines.1, hres⟩
        isplitl [Hroots]
        · isimp only [VectorOwns, UniformVector.owns]
          iexists (fun i => LatentUniform.value (rT := rT) (roots i))
          isplitl []
          · itrivial
          iexists roots
          iframe Hroots
          itrivial
        isimp only [Bool.not_false, Bool.not_true] at Hcredit
        isimp only [UniformVector.world]
        iframe Hcredit

private theorem half_mass : UniformVector.law (UniformVector.initial 2) halfSpace =
    (2 : ℝ≥0∞)⁻¹ := by
  have heval := MeasureTheory.measurePreserving_eval
    (fun _ : Fin 2 => DyadicPosterior.unitLaw) (0 : Fin 2)
  have hmass := heval.measure_preimage
    (show MeasurableSet (Set.Iio (1 / 2 : ℝ)) from measurableSet_Iio).nullMeasurableSet
  rw [UniformVector.initial_law]
  change (MeasureTheory.Measure.pi (fun _ : Fin 2 => DyadicPosterior.unitLaw))
    ((fun x => x 0) ⁻¹' Set.Iio (1 / 2 : ℝ)) = _
  rw [hmass, DyadicPosterior.unitLaw,
    MeasureTheory.Measure.restrict_apply measurableSet_Iio, Set.inter_comm,
    Set.Ico_inter_Iio]
  norm_num [ENNReal.ofReal_div_of_pos]

private theorem half_mass_ne_zero : UniformVector.law (UniformVector.initial 2) halfSpace ≠ 0 := by
  rw [half_mass]
  exact ENNReal.inv_ne_zero.mpr (by simp)

private abbrev acceptedWorld := Conditioning.model (UniformVector.world 2)
  (UniformVector.initial 2) halfSpace half_mass_ne_zero

private abbrev acceptedView (i : Fin 2) := Conditioning.viewModel (UniformVector.world 2)
  (UniformVector.view i) (UniformVector.view_sameWorld i)
  (UniformVector.initial 2) halfSpace half_mass_ne_zero

private abbrev acceptedOwns (handles : Fin 2 → Val rT) :
    Option (Conditioning.Accepted (UniformVector.world 2) (UniformVector.initial 2) halfSpace) →
      IProp GF := VectorRejection.owns (GF := GF)
  (UniformVector.world 2) (UniformVector.initial 2) halfSpace UniformVector.owns handles

private theorem half_sampler (E : CoPset) :
    IsLatentVectorSpec (GF := GF) E
      pl(&Occil.PSRN.newInsideShape #2 &(acceptHalf : Val rT).fst #())
      acceptedWorld acceptedView none acceptedOwns := by
  classical
  exact PSRNInsideShape.newInsideShape_vectorSpec E 1 halfSpace half_mass_ne_zero acceptHalf
    (acceptHalf_spec E)

private def readThree (left right : Val rT) : Exp rT :=
  .app (.lam (.app (.lam (.app (.lam (.pair (.pair (.bvar 2) (.bvar 1)) (.bvar 0)))
    (.app left.fst (.lit (.int 3))))) (.app right.fst (.lit (.int 5)))))
    (.app left.fst (.lit (.int 8)))

omit [ProbLangDist.IsUniformInt rT] in
theorem three_views {Ω S : Type} [MeasurableSpace Ω] (E : CoPset)
    (D : Model Ω S) (V : Fin 2 → Model Ω S) (P : S → IProp GF)
    (hw : ∀ i, D.SameWorld (V i)) (handles : Fin 2 → Val rT)
    (hc : ∀ i, IsViewSpec E (V i) P (handles i)) (s : S)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ P s ∗ ↯ (∫⁻ x, F x ∂D.posterior s) ∗ R -∗
      tglWp E (readThree (handles 0) (handles 1)) (fun result : Val rT =>
        iprop(∃ (t : S) (I J K : RationalInterval),
          ⌜result = Val.pair (Val.pair (intervalVal I) (intervalVal J)) (intervalVal K) ∧
            D.refines s t ∧ (V 0).Encloses t 8 I ∧
            (V 1).Encloses t 5 J ∧ (V 0).Encloses t 3 K⌝ ∗
          P t ∗ ↯ (∫⁻ x, F x ∂D.posterior t) ∗ R)) := by
  iintro ⟨Hstate, Hcredit, HR⟩
  unfold readThree
  twp_bind pl(&(handles 0).fst #8)
  isimp only [← (hw 0).posterior_eq s] at Hcredit
  iapply (hc 0).wp s 8 F hF _ $$ Hstate Hcredit
  iintro %t %I %⟨hst, hI⟩ Hstate Hcredit
  twp_pure
  twp_bind pl(&(handles 1).fst #5)
  isimp only [(hw 0).posterior_eq t, ← (hw 1).posterior_eq t] at Hcredit
  iapply (hc 1).wp t 5 F hF _ $$ Hstate Hcredit
  iintro %u %J %⟨htu, hJ⟩ Hstate Hcredit
  twp_pure
  twp_bind pl(&(handles 0).fst #3)
  isimp only [(hw 1).posterior_eq u, ← (hw 0).posterior_eq u] at Hcredit
  iapply (hc 0).wp u 3 F hF _ $$ Hstate Hcredit
  iintro %v %K %⟨huv, hK⟩ Hstate Hcredit
  twp_pures
  twp_value
  imodintro
  isimp only [(hw 0).posterior_eq v] at Hcredit
  iexists v, I, J, K
  iframe Hstate Hcredit HR
  ipureintro
  have hst' := (hw 0).refines_iff s t |>.mp hst
  have htu' := (hw 1).refines_iff t u |>.mp htu
  have huv' := (hw 0).refines_iff u v |>.mp huv
  exact ⟨rfl, D.refines_trans hst' (D.refines_trans htu' huv'),
    (V 0).encloses_refines ((hw 0).refines_iff t v |>.mpr
      (D.refines_trans htu' huv')) hI,
    (V 1).encloses_refines ((hw 1).refines_iff u v |>.mpr huv') hJ, hK⟩

example (E : CoPset) (handles : Fin 2 → Val rT) (s)
    (F : (Fin 2 → ℝ) → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :=
  three_views E acceptedWorld acceptedView (acceptedOwns handles)
    (half_sampler (rT := rT) (GF := GF) E).sameWorld handles
    ((half_sampler (rT := rT) (GF := GF) E).coordinate handles) s F hF R

example (E : CoPset) (handles : Fin 2 → Val rT) (s) (R : IProp GF) :=
  three_views E acceptedWorld acceptedView (acceptedOwns handles)
    (half_sampler (rT := rT) (GF := GF) E).sameWorld handles
    ((half_sampler (rT := rT) (GF := GF) E).coordinate handles) s
    (fun _ => ∞) measurable_const R

/-- Actual two-dimensional construction returns the original list and whole conditional world. -/
theorem construct_framed (E : CoPset) (F : (Fin 2 → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (R : IProp GF) :
    ⊢ ↯ (∫⁻ x, F x ∂acceptedWorld.posterior none) ∗ R -∗
      tglWp E pl(&Occil.PSRN.newInsideShape #2 &(acceptHalf : Val rT).fst #())
        (fun v : Val rT => iprop(∃ handles t,
          ⌜v = vectorVal handles ∧ acceptedWorld.refines none t⌝ ∗
          acceptedOwns handles t ∗ ↯ (∫⁻ x, F x ∂acceptedWorld.posterior t) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply (half_sampler (rT := rT) (GF := GF) E).wp F hF _ $$ Hcredit
  iintro %handles %t %ht Hstate Hcredit
  iexists handles, t
  iframe Hstate Hcredit HR
  itrivial

example (E : CoPset) (R : IProp GF) := construct_framed E (fun _ => ∞) measurable_const R

/-- The identified law is the full conditional vector law, not a list of marginals. -/
example : vectorLaw acceptedWorld acceptedView none =
    Rejection.law (UniformVector.law (UniformVector.initial 2)) halfSpace half_mass_ne_zero := by
  change (Rejection.law (UniformVector.law (UniformVector.initial 2)) halfSpace
    half_mass_ne_zero).map (fun x => x) = _
  exact MeasureTheory.Measure.map_id

#print axioms acceptHalf_spec
#print axioms half_sampler
#print axioms half_mass
#print axioms three_views
#print axioms construct_framed
#print axioms SampLib.PSRNInsideShape.newInsideShape_vectorSpec
#print axioms SampLib.UniformVector.uniformVector_latentSpec

end
end ReviewExactLatentVector001
