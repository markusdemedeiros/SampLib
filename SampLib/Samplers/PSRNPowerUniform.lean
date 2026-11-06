import SampLib.LatentUniformRepresentation
import SampLib.LatentRepresentedIntegerPower
import SampLib.LatentRepresentedReciprocal
import SampLib.LatentRoot
import SampLib.LatentRepresentedUnary
import Samplers.PSRN.Uniform

/-! # Rational powers of one shared deferred uniform

`newPowerUniform a b` allocates one uniform `u` and returns a lazy oracle for
`u ^ (a / b)`, for every integer `a` and positive `b`. The actual source builds
`u ^ |a|` by repeated squaring, takes a bisection root unless `b = 1`, and takes a
reciprocal when `a < 0`. A zero exponent returns the constant unit oracle.

The uniform is positive almost surely under every posterior. This gives the root's
comparison domain and the reciprocal's nonzero denominator after all later reads.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNPowerUniform

noncomputable section

open LatentReal

abbrev U := LatentUniform.model

/-- A lazy real over the uniform world, bundled with its exact interval schedule. -/
abbrev Stage := (D : Model ℝ (List Bool)) × Representation D

def power (a : ℕ) : Stage :=
  ⟨IntegerPower.model U a, IntegerPower.representation U LatentUniform.representation a⟩

/-- The source returns the power itself for degree one and a bisection root otherwise. -/
def rooted (a b : ℕ) : Stage :=
  if b = 1 then power a
  else ⟨(power a).1.nthRoot b, ((power a).1.nthRoot b).dyadicRepresentation⟩

def reciprocal (X : Stage) : Stage :=
  ⟨RepresentedReciprocal.model X.1 X.2, RepresentedReciprocal.representation X.1 X.2⟩

/-- The three branches of `powerRational`, selected by the sign of the numerator. -/
def stage (a : ℤ) (b : ℕ) : Stage :=
  if a = 0 then ⟨U.constant 1, Representation.point U 1 1 1 (by decide) (by norm_num)⟩
  else if 0 < a then rooted a.natAbs b
  else reciprocal (rooted a.natAbs b)

abbrev model (a : ℤ) (b : ℕ) : Model ℝ (List Bool) := (stage a b).1

abbrev representation (a : ℤ) (b : ℕ) : Representation (model a b) := (stage a b).2

theorem stage_zero (b : ℕ) :
    stage 0 b = ⟨U.constant 1, Representation.point U 1 1 1 (by decide) (by norm_num)⟩ := by
  simp [stage]

theorem stage_pos {a : ℤ} (b : ℕ) (ha : 0 < a) : stage a b = rooted a.natAbs b := by
  simp [stage, ha.ne', ha]

theorem stage_neg {a : ℤ} (b : ℕ) (ha : a < 0) :
    stage a b = reciprocal (rooted a.natAbs b) := by
  simp [stage, ha.ne, not_lt.mpr ha.le]

theorem rooted_one (a : ℕ) : rooted a 1 = power a := by simp [rooted]

theorem rooted_root (a : ℕ) {b : ℕ} (hb : b ≠ 1) :
    rooted a b = ⟨(power a).1.nthRoot b, ((power a).1.nthRoot b).dyadicRepresentation⟩ := by
  simp [rooted, hb]

section world

theorem power_sameWorld (a : ℕ) : U.SameWorld (power a).1 := IntegerPower.sameWorld U a

theorem rooted_sameWorld (a b : ℕ) : U.SameWorld (rooted a b).1 := by
  unfold rooted
  split
  · exact power_sameWorld a
  · exact (power_sameWorld a).trans ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩

theorem sameWorld (a : ℤ) (b : ℕ) : U.SameWorld (model a b) := by
  unfold model stage
  split
  · exact U.sameWorld_constant 1
  split
  · exact rooted_sameWorld _ _
  · exact (rooted_sameWorld _ _).trans (RepresentedReciprocal.sameWorld _ _)

end world

section mathematics

open MeasureTheory

/-- Every uniform posterior is concentrated on positive reals. -/
theorem ae_pos (p : List Bool) : ∀ᵐ u ∂DyadicPosterior.law p, 0 < u := by
  have hne := (DyadicPosterior.law []).ae_ne 0
  rw [DyadicPosterior.law_nil] at hne
  have hunit : ∀ᵐ u ∂DyadicPosterior.unitLaw, 0 < u := by
    filter_upwards [ae_restrict_mem measurableSet_Ico, hne] with u hu h0
    exact lt_of_le_of_ne hu.1 (Ne.symm h0)
  exact DyadicPosterior.law_absolutelyContinuous_unit p |>.ae_le hunit

theorem power_value (a : ℕ) (u : ℝ) : (power a).1.value u = u ^ a :=
  IntegerPower.value_eq U a u

theorem rooted_value (a b : ℕ) (hb : 0 < b) {u : ℝ} (hu : 0 ≤ u) :
    (rooted a b).1.value u = u ^ ((a : ℝ) / b) := by
  unfold rooted
  split
  · subst b
    simp [power_value]
  · change root b ((power a).1.value u) = _
    rw [power_value, root, ← Real.rpow_natCast, ← Real.rpow_mul hu, div_eq_mul_inv]

/-- On the positive half-line every branch computes the real power `u ^ (a / b)`. -/
theorem model_value (a : ℤ) {b : ℕ} (hb : 0 < b) {u : ℝ} (hu : 0 < u) :
    (model a b).value u = u ^ ((a : ℝ) / b) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [model, stage_neg b ha]
    change 1 / (rooted a.natAbs b).1.value u = _
    rw [rooted_value _ _ hb hu.le, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast ha),
      one_div, ← Real.rpow_neg hu.le, neg_div, neg_neg]
  · simp [model, stage_zero, Model.constant]
  · rw [model, stage_pos b ha, rooted_value _ _ hb hu.le, Nat.cast_natAbs, Int.cast_abs,
      abs_of_pos (by exact_mod_cast ha)]

/-- The output law is the image of the unit uniform under `u ↦ u ^ (a / b)`. -/
theorem initial_law (a : ℤ) {b : ℕ} (hb : 0 < b) :
    (model a b).law [] = DyadicPosterior.unitLaw.map (fun u => u ^ ((a : ℝ) / b)) := by
  rw [Model.law, (sameWorld a b).posterior_eq]
  change (DyadicPosterior.law []).map _ = _
  rw [DyadicPosterior.law_nil]
  apply Measure.map_congr
  have hpos := ae_pos []
  rw [DyadicPosterior.law_nil] at hpos
  filter_upwards [hpos] with u hu
  exact model_value a hb hu

/-- The power avoids every rational root threshold, so the bisection terminates. -/
theorem admissible (a b : ℕ) (ha : 0 < a) (p : List Bool) :
    Root.Admissible (power a).1 b p := by
  rw [Root.Admissible, (power_sameWorld a).posterior_eq]
  refine ⟨?_, fun c d _ _ => ?_⟩
  · filter_upwards [ae_pos p] with u hu
    rw [power_value]
    positivity
  · filter_upwards [ae_pos p, (DyadicPosterior.law p).ae_ne ((((c : ℝ) / d) ^ b) ^ (a⁻¹ : ℝ))]
      with u hu hne heq
    rw [power_value] at heq
    exact hne (by rw [← heq, Real.pow_rpow_inv_natCast hu.le ha.ne'])

/-- Every posterior keeps the reciprocal's denominator away from zero. -/
theorem rooted_nonzero (a b : ℕ) (hb : 0 < b) (p : List Bool) :
    ∀ᵐ u ∂(rooted a b).1.posterior p, (rooted a b).1.value u ≠ 0 := by
  rw [(rooted_sameWorld a b).posterior_eq]
  filter_upwards [ae_pos p] with u hu
  rw [rooted_value a b hb hu.le]
  exact (Real.rpow_pos_of_pos hu _).ne'

/-- No branch vanishes, so the actual reciprocal of any power uniform terminates. -/
theorem model_nonzero (a : ℤ) {b : ℕ} (hb : 0 < b) (p : List Bool) :
    ∀ᵐ u ∂(model a b).posterior p, (model a b).value u ≠ 0 := by
  rw [(sameWorld a b).posterior_eq]
  filter_upwards [ae_pos p] with u hu
  rw [model_value a hb hu]
  exact (Real.rpow_pos_of_pos hu _).ne'

end mathematics

namespace Program

private instance uniform_closed {rT : Type} : ClosedExp (Occil.PSRN.newUniform : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance powerRational_closed {rT : Type} :
    ClosedExp (Occil.PSRN.powerRational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance rational_closed {rT : Type} : ClosedExp (Occil.PSRN.rational : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance root_closed {rT : Type} : ClosedExp (Occil.PSRN.root : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance reciprocal_closed {rT : Type} : ClosedExp (Occil.PSRN.reciprocal : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

private instance power_closed {rT : Type} : ClosedExp (Occil.PSRN.integerPowerReal : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

/-- The root constructor: guard the degree, return the source for degree one. -/
def rootBody {rT : Type} : Exp rT :=
  .cond (.binop .le (.bvar 0) (.lit (.int 0))) .fail
    (.cond (.binop .eq (.bvar 0) (.lit (.int 1))) (.bvar 1) (.lam Root.Program.observerBody))

theorem root_eq {rT : Type} : (Occil.PSRN.root : Exp rT) = CurriedStep.lambdas 2 rootBody := by
  kernel_rfl

theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

theorem rootBody_lcb {rT : Type} : Exp.lcb 2 (rootBody : Exp rT) = true := by kernel_rfl

end Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A power closure owns exactly the one uniform cache it multiplies. -/
def powerOwns (a : ℕ) (v : Val rT) (p : List Bool) : IProp GF :=
  iprop(∃ source : Val rT,
    ViewOwns (IntegerPower.value source a) (LatentUniform.owns source) v p)

def rootedOwns (a b : ℕ) : Val rT → List Bool → IProp GF :=
  if b = 1 then powerOwns a else Root.owns (power a).1 b (powerOwns a)

/-- The constant branch owns nothing; the others retain the uniform through each closure. -/
def owns (a : ℤ) (b : ℕ) : Val rT → List Bool → IProp GF :=
  if a = 0 then ViewOwns (LatentRational.value 1 1) (fun _ => iprop(emp))
  else if 0 < a then rootedOwns a.natAbs b
  else RepresentedReciprocal.owns (rooted a.natAbs b).1 (rootedOwns a.natAbs b)

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem owns_zero (b : ℕ) :
    owns (GF := GF) 0 b = ViewOwns (LatentRational.value (rT := rT) 1 1) (fun _ => iprop(emp)) := by
  simp [owns]

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem owns_pos {a : ℤ} (b : ℕ) (ha : 0 < a) :
    owns (rT := rT) (GF := GF) a b = rootedOwns a.natAbs b := by
  simp [owns, ha.ne', ha]

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem owns_neg {a : ℤ} (b : ℕ) (ha : a < 0) :
    owns (rT := rT) (GF := GF) a b =
      RepresentedReciprocal.owns (rooted a.natAbs b).1 (rootedOwns a.natAbs b) := by
  simp [owns, ha.ne, not_lt.mpr ha.le]

theorem powerOracleSpec (E : CoPset) (a : ℕ) :
    IsRepresentedOracleSpec (GF := GF) E (power a).1 (power a).2 (powerOwns a) := by
  refine ⟨fun v p n F hF => ?_⟩
  simp only [power]
  iintro ⟨Hstate, Hcredit⟩
  isimp only [powerOwns] at Hstate
  icases Hstate with ⟨%source, Hstate⟩
  have hpower := IntegerPower.oracleSpec E U LatentUniform.representation
    (LatentUniform.owns source) source
    ((LatentUniform.representedOracleSpec (rT := rT) (GF := GF) E).viewSpec source) a
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hv, Hstate⟩
  subst v
  iapply hpower.wp p n F hF _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  iexists t, I
  isplitl []
  · ipureintro
    exact ⟨rfl, hI⟩
  iframe Hcredit
  isimp only [powerOwns]
  iexists source
  isimp only [ViewOwns]
  iframe Hstate

theorem rootedOracleSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) :
    IsRepresentedOracleSpec (GF := GF) E (rooted a b).1 (rooted a b).2 (rootedOwns a b) := by
  by_cases h1 : b = 1
  · subst b
    rw [show rootedOwns (rT := rT) (GF := GF) a 1 = powerOwns a by simp [rootedOwns],
      rooted_one]
    exact powerOracleSpec E a
  · rw [show rootedOwns (rT := rT) (GF := GF) a b = Root.owns (power a).1 b (powerOwns a) by
      simp [rootedOwns, h1], rooted_root a h1]
    exact Root.representedOracleSpec E (power a).1
      (IntegerPower.measurableError U (fun _ => measurable_const) a) (powerOwns a)
      (powerOracleSpec E a).forget b (by omega)

/-- Every read observes the one shared uniform through the selected branch. -/
theorem representedOracleSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsRepresentedOracleSpec (GF := GF) E (model a b) (representation a b) (owns a b) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [owns_neg b ha]
    unfold model representation
    rw [stage_neg b ha]
    exact RepresentedReciprocal.oracleSpec E _ _ _ (rootedOracleSpec E _ b hb)
  · rw [owns_zero b]
    unfold model representation
    rw [stage_zero b]
    exact represented_point_viewSpec E U _ 1 1 1 (by decide) (by norm_num)
  · rw [owns_pos b ha]
    unfold model representation
    rw [stage_pos b ha]
    exact rootedOracleSpec E _ b hb

omit [ProbLangDist.IsUniformInt rT] in
/-- A degree-one root returns its source handle unchanged. -/
theorem twp_root_one (E : CoPset) (source : Val rT) (P : List Bool → IProp GF) (p : List Bool) :
    P p ⊢ tglWp E pl(&Occil.PSRN.root &source.fst #1)
      (fun v => ViewOwns source P v p) := by
  have h := CurriedStep.twp_apply E [] [source, .int 1] Program.rootBody
    (Program.rootBody_lcb (rT := rT)) (fun v => ViewOwns source P v p)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ← Program.root_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem,
    Exp.ofVal] at h
  iintro Hstate
  iapply h
  simp only [CurriedStep.opened, Program.rootBody, List.length_cons, List.length_nil,
    Exp.openRec, Val.int, Nat.reduceAdd, ↓reduceIte, Nat.succ_ne_self,
    ← Exp.open_lc 0 _ source.fst source.lc]
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  ieval (change _ ⊢ tglWp E (Exp.ofVal source) _)
  iapply tglWp_value
  isimp only [ViewOwns]
  iframe Hstate

omit [ProbLangDist.IsUniformInt rT] in
/-- The source's positive-power branch: repeated squaring, then a root unless `b = 1`. -/
theorem twp_rooted (E : CoPset) (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (source : Val rT)
    (p : List Bool) :
    LatentUniform.owns source p ⊢
      tglWp E pl(&Occil.PSRN.root (&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        #int (b : ℤ)) (fun v => rootedOwns n b v p) := by
  iintro Hstate
  twp_bind pl(&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply IntegerPower.twp_integerPowerReal E source (LatentUniform.owns source) p n $$ Hstate
  iintro %power Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hpower, Hstate⟩
  subst power
  simp only [Exp.ofVal]
  by_cases h1 : b = 1
  · subst b
    rw [show rootedOwns (rT := rT) (GF := GF) n 1 = powerOwns n by simp [rootedOwns],
      Nat.cast_one]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_root_one E (IntegerPower.value source n) (LatentUniform.owns source) p
        $$ Hstate
    iintro %v Hstate
    isimp only [powerOwns]
    iexists source
    iexact Hstate
  · rw [show rootedOwns (rT := rT) (GF := GF) n b = Root.owns (power n).1 b (powerOwns n) by
      simp [rootedOwns, h1]]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply Root.Program.twp_root E (IntegerPower.value source n) b (by omega)
        (powerOwns n (IntegerPower.value source n)) p
      isimp only [powerOwns]
      iexists source
      isimp only [ViewOwns]
      iframe Hstate
    iintro %v Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    isimp only [Root.owns]
    iexists IntegerPower.value source n
    iframe Hstate
    ipureintro
    exact ⟨hv, admissible n b hn p⟩

theorem newPowerUniform_representedDistSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newPowerUniform #a #int (b : ℤ) #())
      (model a b) (representation a b) [] (owns a b) where
  oracle := representedOracleSpec E a b hb
  spec F hF := by
    iintro Hcredit
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_pure
    rw [decide_eq_false (by omega)]
    twp_pure
    twp_bind pl(&Occil.PSRN.newUniform #())
    isimp only [(sameWorld a b).posterior_eq] at Hcredit
    iapply ((LatentUniform.newUniform_representedDistSpec E).toIsLatentPayloadSpec.wp F hF _)
      $$ Hcredit
    iintro %source %p %hp Hstate Hcredit
    twp_pure
    simp only [ClosedExp.openRec]
    iterate 3 twp_pure
    simp only [ClosedExp.openRec, ClosedExp.closeRec]
    twp_pure
    rw [decide_eq_false (by omega)]
    twp_pure
    twp_pure
    rw [Program.int_beq]
    rcases lt_trichotomy a 0 with ha | rfl | ha
    · -- Negative exponent: the reciprocal of the positive branch.
      obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat ha.le
      have hn : 0 < n := by omega
      rw [beq_eq_false_iff_ne.mpr ha.ne]
      twp_pure
      twp_pure
      rw [decide_eq_true ha]
      twp_pure
      twp_pure
      rw [neg_neg]
      twp_bind pl(&Occil.PSRN.root (&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        #int (b : ℤ))
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply twp_rooted E n b hn hb source p $$ Hstate
      iintro %root Hstate
      simp only [Exp.ofVal]
      iapply tglWp_wand
      isplitl [Hstate Hcredit]
      · iapply RepresentedReciprocal.twp_reciprocal E (rooted n b).1 (rooted n b).2
          (rootedOwns n b) root p (rooted_nonzero n b hb p) F
        isimp only [(rooted_sameWorld n b).posterior_eq]
        iframe Hstate Hcredit
      iintro %v ⟨Hstate, Hcredit⟩
      iexists p
      rw [owns_neg b ha, Int.natAbs_neg, Int.natAbs_natCast]
      isimp only [(sameWorld _ b).posterior_eq]
      isimp only [(RepresentedReciprocal.sameWorld (rooted n b).1 (rooted n b).2).posterior_eq,
        (rooted_sameWorld n b).posterior_eq] at Hcredit
      iframe Hstate Hcredit
      ipureintro
      exact ((sameWorld _ b).refines_iff _ _).mpr hp
    · -- Zero exponent: the constant unit oracle; the allocated cache is not needed.
      rw [show ((0 : ℤ) == 0) = true from rfl]
      twp_pure
      twp_pures
      ieval (change _ ⊢ tglWp E (Exp.ofVal (LatentRational.value 1 1)) _)
      iapply tglWp_value
      iexists p
      rw [owns_zero b]
      isimp only [(sameWorld 0 b).posterior_eq, ViewOwns]
      iframe Hcredit
      iclear Hstate
      ipureintro
      exact ⟨((sameWorld 0 b).refines_iff _ _).mpr hp, trivial, trivial⟩
    · -- Positive exponent.
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha.le
      have hn : 0 < n := by omega
      rw [beq_eq_false_iff_ne.mpr ha.ne']
      twp_pure
      twp_pure
      twp_pure
      iapply tglWp_wand
      isplitl [Hstate]
      · iapply twp_rooted E n b hn hb source p $$ Hstate
      iintro %v Hstate
      iexists p
      rw [owns_pos b ha, Int.natAbs_natCast]
      isimp only [(sameWorld _ b).posterior_eq]
      iframe Hstate Hcredit
      ipureintro
      exact ((sameWorld _ b).refines_iff _ _).mpr hp

/-- Standard latent-law interface, including arbitrary future shared observations. -/
theorem newPowerUniform_latentDistSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newPowerUniform #a #int (b : ℤ) #())
      (model a b) [] (owns a b) :=
  (newPowerUniform_representedDistSpec E a b hb).forget

end specification

end

end SampLib.PSRNPowerUniform
