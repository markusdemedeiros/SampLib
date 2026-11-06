import SampLib.Syntax.PSRNJohnkBeta
import SampLib.Latent.LatentRepresentedDivision
import SampLib.Latent.LatentRepresentedAddition
import SampLib.Latent.LatentProduct
import SampLib.Latent.LatentConditionedOracle
import SampLib.Latent.LatentRejectionKernel
import SampLib.PSRN.Support.PSRNLess
import SampLib.PSRN.Laws.JohnkBeta

/-! # Johnk's beta rejection over two independent deferred proposals

The two power proposals allocate independent worlds. Their sum and the constant one
are views of that product world, so the strict comparison refines the same pair that
the returned quotient later observes. Accepted states retain both proposal caches.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNJohnkBeta

noncomputable section

open LatentReal

variable {ΩX ΩY SX SY : Type} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
variable (X : Model ΩX SX) (Y : Model ΩY SY)

/-- The proposal sum, as a view of the joint proposal world. -/
def sum : Model (ΩX × ΩY) (SX × SY) :=
  (ProductModel.left X Y).add (ProductModel.right X Y) (ProductModel.sameWorld X Y)

/-- The source's comparison threshold `rational 1 1`. -/
def one : Model (ΩX × ΩY) (SX × SY) :=
  (ProductModel.left X Y).constant (((1 : ℤ) : ℝ) / (1 : ℤ))

theorem left_sameWorld_sum : (ProductModel.left X Y).SameWorld (sum X Y) :=
  Model.SameWorld.add_left (ProductModel.sameWorld X Y)

theorem sum_sameWorld_one : (sum X Y).SameWorld (one X Y) :=
  Model.SameWorld.between (left_sameWorld_sum X Y) (Model.sameWorld_constant _ _)

/-- Johnk's acceptance event `x + y < 1`. -/
def accepted : Set (ΩX × ΩY) := Less.event (sum X Y) (one X Y)

instance : DecidablePred (· ∈ accepted X Y) := Less.eventDecidable _ _

section representation

open MeasureTheory

variable {X Y}

/-- The first proposal's intervals, read through the product world. -/
def leftRepresentation (R : Representation X) : Representation (ProductModel.left X Y) where
  interval n z := R.interval n z.1
  measurable_lower n := (R.measurable_lower n).comp measurable_fst
  measurable_upper n := (R.measurable_upper n).comp measurable_fst
  measurable_denominator n := (R.measurable_denominator n).comp measurable_fst
  approximates s :=
    (Measure.quasiMeasurePreserving_fst (μ := X.posterior s.1) (ν := Y.posterior s.2)).ae
      (R.approximates s.1)

/-- The second proposal's intervals, read through the product world. -/
def rightRepresentation (R : Representation Y) : Representation (ProductModel.right X Y) where
  interval n z := R.interval n z.2
  measurable_lower n := (R.measurable_lower n).comp measurable_snd
  measurable_upper n := (R.measurable_upper n).comp measurable_snd
  measurable_denominator n := (R.measurable_denominator n).comp measurable_snd
  approximates s :=
    (Measure.quasiMeasurePreserving_snd (μ := X.posterior s.1) (ν := Y.posterior s.2)).ae
      (R.approximates s.2)

def sumRepresentation (RX : Representation X) (RY : Representation Y) :
    Representation (sum X Y) :=
  Representation.add _ _ (ProductModel.sameWorld X Y) (leftRepresentation RX)
    (rightRepresentation RY)

variable (X Y) in
/-- The returned quotient `x / (x + y)`, still a view of the joint proposal world. -/
def ratio (RX : Representation X) (RY : Representation Y) : Model (ΩX × ΩY) (SX × SY) :=
  RepresentedDivision.model (ProductModel.left X Y) (sum X Y) (left_sameWorld_sum X Y)
    (sumRepresentation RX RY)

end representation

section mathematics

open MeasureTheory ProbabilityTheory Set
open ENNReal (ofReal)

variable {X Y} {a b : ℝ} {i : SX} {j : SY}

/-- The joint proposal posterior pushes forward to the two independent proposal laws. -/
private theorem map_pair :
    (ProductModel.posterior X Y (i, j)).map (Prod.map X.value Y.value) =
      (X.law i).prod (Y.law j) :=
  ProductModel.law_eq_product X Y (i, j)

private theorem measurable_pair : Measurable (Prod.map X.value Y.value) :=
  X.measurable_value.prodMap Y.measurable_value

/-- An atomless second coordinate makes every level set of the sum null. -/
private theorem ae_sum_ne (hb : 0 < b) (μ : Measure ℝ) [SFinite μ] (c : ℝ) :
    ∀ᵐ p ∂μ.prod (betaMeasure b 1), p.1 + p.2 ≠ c := by
  have hset : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ≠ c} :=
    (measurableSet_eq_fun (by fun_prop) measurable_const).compl
  let := isProbabilityMeasureBeta hb zero_lt_one
  rw [Measure.ae_prod_iff_ae_ae hset]
  refine Filter.Eventually.of_forall fun x => ?_
  have hnull : betaMeasure b 1 {c - x} = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_singleton _)
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  simp only [ne_eq, Decidable.not_not] at hy
  rw [mem_singleton_iff]
  linarith [show x + y = c from hy]

/-- Each proposal sum avoids any fixed value almost surely, at every refined state. -/
theorem sum_ne (hb : 0 < b) (hY : Y.law j = betaMeasure b 1) (c : ℝ) :
    ∀ᵐ z ∂ProductModel.posterior X Y (i, j), (sum X Y).value z ≠ c := by
  have h : ∀ᵐ p ∂(ProductModel.posterior X Y (i, j)).map (Prod.map X.value Y.value),
      p.1 + p.2 ≠ c := by
    rw [map_pair, hY]
    exact ae_sum_ne hb _ c
  exact ae_of_ae_map measurable_pair.aemeasurable h

/-- Refined states inherit the null level sets of the initial proposal sum. -/
theorem sum_ne_of_refines (hb : 0 < b) (hY : Y.law j = betaMeasure b 1) (c : ℝ)
    {u : SX × SY} (hu : (ProductModel.left X Y).refines (i, j) u) :
    ∀ᵐ z ∂ProductModel.posterior X Y u, (sum X Y).value z ≠ c :=
  ((ProductModel.left X Y).absolutelyContinuous hu).ae_le (sum_ne hb hY c)

private theorem accepted_eq :
    accepted X Y = Prod.map X.value Y.value ⁻¹' {p : ℝ × ℝ | p.1 + p.2 < 1} := by
  ext z
  simp [accepted, Less.event, sum, one, Model.add, Model.constant, ProductModel.left,
    ProductModel.right]

private theorem measurableSet_lt_one : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 < 1} :=
  measurableSet_lt (by fun_prop) measurable_const

/-- Johnk's acceptance probability `a b / (a + b) * B(a, b)`. -/
theorem acceptance_mass (ha : 0 < a) (hb : 0 < b) (hX : X.law i = betaMeasure a 1)
    (hY : Y.law j = betaMeasure b 1) :
    ProductModel.posterior X Y (i, j) (accepted X Y) = ofReal (JohnkBeta.acceptance a b) := by
  have hmap := congrArg (fun ν : Measure ℝ => ν univ) (JohnkBeta.accepted_map a b ha hb)
  let := isProbabilityMeasureBeta ha hb
  simp only [Measure.map_apply (by fun_prop : Measurable fun z : ℝ × ℝ => z.1 / (z.1 + z.2))
    MeasurableSet.univ, preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at hmap
  rw [accepted_eq, ← Measure.map_apply measurable_pair measurableSet_lt_one, map_pair, hX, hY,
    hmap]

theorem acceptance_ne_zero (ha : 0 < a) (hb : 0 < b) (hX : X.law i = betaMeasure a 1)
    (hY : Y.law j = betaMeasure b 1) :
    ProductModel.posterior X Y (i, j) (accepted X Y) ≠ 0 := by
  rw [acceptance_mass ha hb hX hY]
  exact (ENNReal.ofReal_pos.mpr (JohnkBeta.acceptance_pos a b ha hb)).ne'

variable (X Y) in
/-- The returned quotient under the proposal posterior conditioned on acceptance. -/
def model (RX : Representation X) (RY : Representation Y) (i : SX) (j : SY)
    (hmass : ProductModel.posterior X Y (i, j) (accepted X Y) ≠ 0) :
    Model (ΩX × ΩY) (Option (Conditioning.Accepted (ratio X Y RX RY) (i, j) (accepted X Y))) :=
  Conditioning.model (ratio X Y RX RY) (i, j) (accepted X Y) hmass

private theorem ratio_value (RX : Representation X) (RY : Representation Y) :
    (ratio X Y RX RY).value =
      (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ∘ Prod.map X.value Y.value := by
  funext z
  exact RepresentedDivision.value_eq _ _ _ _ z

/-- Normalizing the accepted proposal pairs gives the canonical beta law. -/
theorem model_law (ha : 0 < a) (hb : 0 < b) (hX : X.law i = betaMeasure a 1)
    (hY : Y.law j = betaMeasure b 1) (RX : Representation X) (RY : Representation Y)
    (hmass : ProductModel.posterior X Y (i, j) (accepted X Y) ≠ 0) :
    (model X Y RX RY i j hmass).law none = betaMeasure a b := by
  have hg : Measurable fun p : ℝ × ℝ => p.1 / (p.1 + p.2) := by fun_prop
  change (Rejection.law (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass).map
    (ratio X Y RX RY).value = _
  rw [Rejection.law, Measure.map_smul _ (ratio X Y RX RY).measurable_value.aemeasurable,
    ratio_value, ← Measure.map_map hg measurable_pair,
    acceptance_mass ha hb hX hY, accepted_eq,
    ← Measure.restrict_map measurable_pair measurableSet_lt_one, map_pair, hX, hY]
  exact JohnkBeta.normalized_map a b ha hb

variable (hmass : ProductModel.posterior X Y (i, j) (accepted X Y) ≠ 0)

/-- Accepted pairs carry output credit; rejected pairs fund an amplified retry. -/
def branch (F : ΩX × ΩY → ℝ≥0∞) (ε : ℝ≥0∞) : Bool → ΩX × ΩY → ℝ≥0∞ :=
  LatentRejectionKernel.branchCredit (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass F ε

theorem measurable_branch {F : ΩX × ΩY → ℝ≥0∞} (hF : Measurable F) (ε : ℝ≥0∞) (c : Bool) :
    Measurable (branch hmass F ε c) := by
  cases c
  · exact measurable_const
  · exact hF

/-- The credit of a fresh proposal pair, before the comparison is observed. -/
def guarded (F : ΩX × ΩY → ℝ≥0∞) (ε : ℝ≥0∞) : ΩX × ΩY → ℝ≥0∞ :=
  Less.outputCredit (sum X Y) (one X Y) (branch hmass F ε)

theorem loop_expectation (F : ΩX × ΩY → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ z, guarded hmass F ε z ∂ProductModel.posterior X Y (i, j) ≤
      Rejection.credit (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass F + ε :=
  LatentRejectionKernel.expectation_preservation _ _ hmass (Less.measurableSet_event _ _) F ε

theorem measurable_guarded {F : ΩX × ΩY → ℝ≥0∞} (hF : Measurable F) (ε : ℝ≥0∞) :
    Measurable (guarded hmass F ε) := by
  have heq : guarded hmass F ε = fun z => if z ∈ accepted X Y then F z else
      Rejection.credit (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass F +
        Rejection.terminationFactor (ProductModel.posterior X Y (i, j)) (accepted X Y) * ε := by
    funext z
    by_cases h : z ∈ accepted X Y <;>
      simp [guarded, Less.outputCredit, branch, LatentRejectionKernel.branchCredit, accepted, h]
  rw [heq]
  exact Measurable.ite (Less.measurableSet_event _ _) hF measurable_const

theorem accept_credit (ν : Measure (ΩX × ΩY)) (F : ΩX × ΩY → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ z, branch hmass F ε true z ∂ν = ∫⁻ z, F z ∂ν := by
  simp only [branch, LatentRejectionKernel.branchCredit, ite_true]

theorem retry_credit (ν : Measure (ΩX × ΩY)) [IsProbabilityMeasure ν]
    (F : ΩX × ΩY → ℝ≥0∞) (ε : ℝ≥0∞) :
    ∫⁻ z, branch hmass F ε false z ∂ν =
      Rejection.credit (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass F +
        Rejection.terminationFactor (ProductModel.posterior X Y (i, j)) (accepted X Y) * ε := by
  simp [branch, LatentRejectionKernel.branchCredit]

theorem amplification (hmass : ProductModel.posterior X Y (i, j) (accepted X Y) ≠ 0) :
    1 < Rejection.terminationFactor (ProductModel.posterior X Y (i, j)) (accepted X Y) :=
  lt_add_of_pos_right 1 (ENNReal.toNNReal_pos hmass (measure_ne_top _ _))

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

variable {X Y}

/-- Reading the first proposal retains the second cache and the joint credit. -/
theorem left_viewSpec (E : CoPset) (RX : Representation X)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (hX : IsRepresentedOracleSpec E X RX OX) (x y : Val rT) :
    IsRepresentedViewSpec E (ProductModel.left X Y) (leftRepresentation RX)
      (Product.owns OX OY x y) x where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, Product.owns] at Hstate
    icases Hstate with ⟨%hv, Hleft, Hright⟩
    subst v
    isimp only [ProductModel.left, ProductModel.expectation_left X Y s F hF] at Hcredit
    iapply hX.wp x s.1 n (ProductModel.leftCredit Y s.2 F)
      (ProductModel.measurable_leftCredit Y s.2 hF) _ $$ Hleft Hcredit
    iintro %t %I %hI Hleft Hcredit
    isimp only [← ProductModel.expectation_left X Y (t, s.2) F hF] at Hcredit
    iexists (t, s.2), I
    isplit
    · ipureintro
      exact ⟨rfl, ⟨hI.1, Y.refines_refl _⟩, ProductModel.encloses_left X Y s.2 hI.2.1,
        (MeasureTheory.Measure.quasiMeasurePreserving_fst
          (μ := X.posterior t) (ν := Y.posterior s.2)).ae hI.2.2⟩
    isimp only [ViewOwns, Product.owns, ProductModel.left]
    iframe Hleft Hright Hcredit

/-- Reading the second proposal uses the other Tonelli order. -/
theorem right_viewSpec (E : CoPset) (RY : Representation Y)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (hY : IsRepresentedOracleSpec E Y RY OY) (x y : Val rT) :
    IsRepresentedViewSpec E (ProductModel.right X Y) (rightRepresentation RY)
      (Product.owns OX OY x y) y where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [ViewOwns, Product.owns] at Hstate
    icases Hstate with ⟨%hv, Hleft, Hright⟩
    subst v
    isimp only [ProductModel.right, ProductModel.left,
      ProductModel.expectation_right X Y s F hF] at Hcredit
    iapply hY.wp y s.2 n (ProductModel.rightCredit X s.1 F)
      (ProductModel.measurable_rightCredit X s.1 hF) _ $$ Hright Hcredit
    iintro %t %I %hI Hright Hcredit
    isimp only [← ProductModel.expectation_right X Y (s.1, t) F hF] at Hcredit
    iexists (s.1, t), I
    isplit
    · ipureintro
      exact ⟨rfl, ⟨X.refines_refl _, hI.1⟩, ProductModel.encloses_right X Y s.1 hI.2.1,
        (MeasureTheory.Measure.quasiMeasurePreserving_snd
          (μ := X.posterior s.1) (ν := Y.posterior t)).ae hI.2.2⟩
    isimp only [ViewOwns, Product.owns, ProductModel.right, ProductModel.left]
    iframe Hleft Hright Hcredit

theorem sum_measurableError (hXe : X.MeasurableError) (hYe : Y.MeasurableError) :
    (sum X Y).MeasurableError := by
  have hl : (ProductModel.left X Y).MeasurableError := fun n => (hXe n).comp measurable_fst
  have hr : (ProductModel.right X Y).MeasurableError := fun n => (hYe n).comp measurable_snd
  exact hl.add hr _

theorem sum_viewSpec (E : CoPset) (RX : Representation X) (RY : Representation Y)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (hX : IsRepresentedOracleSpec E X RX OX) (hY : IsRepresentedOracleSpec E Y RY OY)
    (x y : Val rT) :
    IsRepresentedViewSpec E (sum X Y) (sumRepresentation RX RY)
      (Product.owns OX OY x y) (addVal x y) :=
  represented_add_oracleSpec E _ _ (ProductModel.sameWorld X Y) _ _ _ x y
    (left_viewSpec E RX OX OY hX x y) (right_viewSpec E RY OX OY hY x y)

/-- The accepted quotient owns both proposals; its denominator is almost surely nonzero. -/
def rawOwns (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (v : Val rT) (s : SX × SY) : IProp GF :=
  iprop(∃ (x y : Val rT), ⌜v = RepresentedDivision.value x (addVal x y)⌝ ∗
    withInvariant (RepresentedReciprocalView.Nonzero (sum X Y)) (Product.owns OX OY x y) s)

theorem raw_oracleSpec (E : CoPset) (RX : Representation X) (RY : Representation Y)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (hX : IsRepresentedOracleSpec E X RX OX) (hY : IsRepresentedOracleSpec E Y RY OY) :
    IsOracleSpec E (ratio X Y RX RY) (rawOwns (X := X) (Y := Y) OX OY) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [rawOwns] at Hstate
    icases Hstate with ⟨%x, %y, %hv, Hstate⟩
    subst v
    have hview := (RepresentedDivision.viewSpec E (ProductModel.left X Y) (sum X Y)
      (left_sameWorld_sum X Y) (leftRepresentation RX) (sumRepresentation RX RY)
      (Product.owns OX OY x y) x (addVal x y) (left_viewSpec E RX OX OY hX x y)
      (sum_viewSpec E RX RY OX OY hX hY x y)).forget
    isimp only [ratio] at Hcredit
    iapply IsViewSpec.wp hview s n F hF _ $$ Hstate Hcredit
    iintro %t %I %hI Hstate Hcredit
    iexists t, I
    isplit
    · ipureintro
      exact ⟨rfl, hI⟩
    isplitl [Hstate]
    · isimp only [rawOwns]
      iexists x, y
      iframe Hstate
      itrivial
    isimp only [ratio]
    iexact Hcredit

def owns (RX : Representation X) (RY : Representation Y) (i : SX) (j : SY)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF) :
    Val rT → Option (Conditioning.Accepted (ratio X Y RX RY) (i, j) (accepted X Y)) →
      IProp GF :=
  Conditioning.owns (ratio X Y RX RY) (i, j) (accepted X Y) (rawOwns (X := X) (Y := Y) OX OY)

open scoped SampLib.PSRNJohnkBeta.Program

/-- The actual retry loop returns the accepted quotient under the conditional law. -/
theorem twp_loop (E : CoPset) (an ad bn bd : ℤ) {b : ℝ} (hb : 0 < b)
    (RX : Representation X) (RY : Representation Y) (i : SX) (j : SY)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (hX : IsRepresentedDistSpec E pl(&Occil.PSRN.newPowerUniform #ad #an #()) X RX i OX)
    (hY : IsRepresentedDistSpec E pl(&Occil.PSRN.newPowerUniform #bd #bn #()) Y RY j OY)
    (hXe : X.MeasurableError) (hYe : Y.MeasurableError) (hYlaw : Y.law j = ProbabilityTheory.betaMeasure b 1)
    (hmass : ProductModel.posterior X Y (i, j) (accepted X Y) ≠ 0)
    (F : ΩX × ΩY → ℝ≥0∞) (hF : Measurable F) :
    iprop(↯ (Rejection.credit (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass F)) ⊢
      tglWp E (.app (Program.loop an ad bn bd) (.lit .unit))
        (fun v : Val rT => iprop(∃ q, ⌜(model X Y RX RY i j hmass).refines none q⌝ ∗
          owns RX RY i j OX OY v q ∗
          ↯ (∫⁻ z, F z ∂(model X Y RX RY i j hmass).posterior q))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %ε %hε Hterm
  irevert Hcredit
  iapply ErrorCredit.Induction.simple hε (amplification hmass) $$ [] Hterm
  iintro !> ⟨IH, Hterm⟩ Hcredit
  twp_pure
  isimp only [ClosedExp.openRec]
  twp_pure
  isimp only [ClosedExp.openRec]
  have hG := measurable_guarded hmass hF ε
  icombine Hcredit Hterm as Hcredit
  -- Two independent proposals, with the joint credit split by Tonelli.
  ihave Hcredit := ErrorCredit.weaken ((ProductModel.expectation_left X Y (i, j) (guarded hmass F ε) hG).ge.trans
    (loop_expectation hmass F ε)) $$ Hcredit
  twp_bind pl(&Occil.PSRN.newPowerUniform #ad #an #())
  have hXd := hX.forget
  have hXwp := hXd.wp (ProductModel.leftCredit Y j (guarded hmass F ε)) (ProductModel.measurable_leftCredit Y j hG)
  iapply hXwp $$ Hcredit
  iintro %x %s %hs Hx Hcredit
  ihave Hcredit := ErrorCredit.weaken ((ProductModel.expectation_right X Y (s, j)
    (guarded hmass F ε) hG).symm.trans
    (ProductModel.expectation_left X Y (s, j) (guarded hmass F ε) hG)).le $$ Hcredit
  twp_pure
  isimp only [ClosedExp.openRec]
  twp_bind pl(&Occil.PSRN.newPowerUniform #bd #bn #())
  have hYwp := hY.forget.wp (ProductModel.rightCredit X s (guarded hmass F ε))
    (ProductModel.measurable_rightCredit X s hG)
  iapply hYwp $$ Hcredit
  iintro %y %t %ht Hy Hcredit
  ihave Hcredit := ErrorCredit.weaken
    (ProductModel.expectation_right X Y (s, t) (guarded hmass F ε) hG).le $$ Hcredit
  twp_pure
  isimp only [ClosedExp.openRec]
  -- The sum and the threshold are views of the same proposal pair.
  twp_bind pl(&Occil.PSRN.add &x.fst &y.fst)
  iapply tglWp_wand
  isplitl [Hx Hy]
  · iapply twp_add E x y (Product.owns OX OY x y) (s, t)
    isimp only [Product.owns]
    iframe Hx Hy
  iintro %total Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%htotal, Hstate⟩
  subst total
  twp_pure
  isimp only [ClosedExp.openRec]
  twp_bind pl(&Occil.PSRN.rational #1 #1)
  twp_pures
  twp_value
  imodintro
  -- Compare the sum with one, refining the same proposal pair.
  have hleft := (sum_viewSpec E RX RY OX OY hX.oracle hY.oracle x y).forget
  have hright := (represented_constant_viewSpec E (ProductModel.left X Y)
    (Product.owns OX OY x y) 1 1 one_pos).forget
  have hst : (ProductModel.left X Y).refines (i, j) (s, t) := ⟨hs, ht⟩
  twp_bind pl(&Occil.PSRN.less &(addVal x y).fst &(LatentRational.value (rT := rT) 1 1).fst)
  iapply tglWp_wand
  isplitl [Hstate Hcredit]
  · iapply Less.twp_less E (sum X Y) (one X Y) (sum_sameWorld_one X Y)
      (sum_measurableError hXe hYe) (fun _ => measurable_const) _ (addVal x y)
      (LatentRational.value 1 1) hleft hright (s, t) (sum_ne_of_refines hb hYlaw _ hst)
      (branch hmass F ε) (measurable_branch hmass hF ε)
    have hcredit : ∫⁻ z, Less.outputCredit (sum X Y) (one X Y) (branch hmass F ε) z
        ∂(sum X Y).posterior (s, t) ≤ ∫⁻ z, guarded hmass F ε z ∂ProductModel.posterior X Y (s, t) :=
      le_rfl
    ihave Hcredit := ErrorCredit.weaken hcredit $$ Hcredit
    iframe Hstate Hcredit
  iintro %result Hpost
  isimp only [Less.post] at Hpost
  icases Hpost with ⟨%c, %u, %hu, Hstate, Hcredit⟩
  rcases hu with ⟨rfl, hsu, hevent⟩
  have hu : (ProductModel.left X Y).refines (i, j) u :=
    (ProductModel.left X Y).refines_trans hst hsu
  cases c
  · -- Rejection discards the pair and funds the amplified retry.
    twp_pure
    ihave Hcredit := ErrorCredit.weaken (retry_credit hmass _ F ε).ge $$ Hcredit
    ihave ⟨Hcredit, Hterm⟩ := ErrorCredit.split $$ Hcredit
    ieval (change _ ⊢ tglWp E (.app (Program.loop an ad bn bd) (.lit .unit)) _)
    iapply IH $$ Hterm Hcredit
  · -- Acceptance returns the quotient of the same refined pair.
    twp_pure
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply RepresentedDivision.twp_constructor E (sum X Y) (Product.owns OX OY x y) x
        (addVal x y) u
      isimp only [withInvariant]
      iframe Hstate
      ipureintro
      exact sum_ne_of_refines hb hYlaw 0 hu
    iintro %v Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    have haccepted : ∀ᵐ z ∂(ratio X Y RX RY).posterior u, z ∈ accepted X Y := by
      filter_upwards [hevent] with z hz
      simpa only [decide_eq_true_eq, accepted] using hz
    iexists some ⟨u, hu, haccepted⟩
    isplit
    · ipureintro
      trivial
    isplitl [Hstate]
    · isimp only [owns, Conditioning.owns, rawOwns]
      iexists x, y
      iframe Hstate
      itrivial
    have hcredit : ∫⁻ z, F z ∂(model X Y RX RY i j hmass).posterior (some ⟨u, hu, haccepted⟩) ≤
        ∫⁻ z, branch hmass F ε true z ∂(sum X Y).posterior u :=
      (accept_credit hmass _ F ε).ge
    ihave Hcredit := ErrorCredit.weaken hcredit $$ Hcredit
    iexact Hcredit

/-- Subunit shapes: the actual beta constructor reaches Johnk's loop. Any represented
specifications of the two source power proposals with laws `Beta(a,1)` and `Beta(b,1)`
determine the returned beta draw and its retained proposal caches. -/
theorem newBeta_latentDistSpec (E : CoPset) (an ad bn bd : ℤ) (han : 0 < an) (hab : an < ad)
    (hbn : 0 < bn) (hbb : bn < bd) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (RX : Representation X) (RY : Representation Y) (i : SX) (j : SY)
    (OX : Val rT → SX → IProp GF) (OY : Val rT → SY → IProp GF)
    (hX : IsRepresentedDistSpec E pl(&Occil.PSRN.newPowerUniform #ad #an #()) X RX i OX)
    (hY : IsRepresentedDistSpec E pl(&Occil.PSRN.newPowerUniform #bd #bn #()) Y RY j OY)
    (hXe : X.MeasurableError) (hYe : Y.MeasurableError)
    (hXlaw : X.law i = ProbabilityTheory.betaMeasure a 1)
    (hYlaw : Y.law j = ProbabilityTheory.betaMeasure b 1) :
    IsLatentDistSpec E pl(&Occil.PSRN.newBeta #an #ad #bn #bd #())
      (model X Y RX RY i j (acceptance_ne_zero ha hb hXlaw hYlaw)) none
      (owns RX RY i j OX OY) where
  oracle := Conditioning.oracleSpec E _ _ _ _ _ (raw_oracleSpec E RX RY OX OY hX.oracle hY.oracle)
  spec F hF := by
    iintro Hcredit
    iapply Program.twp_open E an ad bn bd han hab hbn hbb
    have hmass := acceptance_ne_zero ha hb hXlaw hYlaw
    have hcredit : Rejection.credit (ProductModel.posterior X Y (i, j)) (accepted X Y) hmass F ≤
        ∫⁻ z, F z ∂(model X Y RX RY i j hmass).posterior none := le_rfl
    ihave Hcredit := ErrorCredit.weaken hcredit $$ Hcredit
    iapply twp_loop E an ad bn bd hb RX RY i j OX OY hX hY hXe hYe hYlaw hmass F hF $$ Hcredit

end specification

end

end SampLib.PSRNJohnkBeta
