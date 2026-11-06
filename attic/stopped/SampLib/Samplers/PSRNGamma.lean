import SampLib.PSRNGammaCore
import SampLib.PSRNJohnkBeta
import SampLib.Syntax.PSRNGammaSource
import SampLib.PSRN.PSRNGammaInteger
import SampLib.PSRN.PSRNPowerUniform
import SampLib.Distributions.PSRNPowerUniformBeta

/-! # The rational-shape gamma constructor

With `sn = w * sd + r`, the source builds the integer part `w` (a constant zero, or the
integer-shape gamma). A nonzero remainder adds `Beta(r/sd, 1-r/sd) * Exp(rate)`, the
beta drawn by Johnk's subunit branch of the actual beta constructor. The beta-gamma
product identity and gamma additivity give `Gamma(sn/sd, rate)`.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNGamma

noncomputable section

open LatentReal

abbrev rate (a b : ℤ) : ℝ := (a : ℝ) / b

/-! ## The integer part -/

/-- A zero integer part is the constant zero viewed on the depth-zero gamma world. -/
def integerModel (w a b : ℤ) (ha : 0 < a) (hb : 0 < b) :=
  if w = 0 then (PSRNGammaInteger.model w a b ha hb).constant (((0 : ℤ) : ℝ) / (1 : ℤ))
  else PSRNGammaInteger.model w a b ha hb

/-! ## Johnk's beta factor -/

/-- The two power proposals of the beta constructor called with shapes `r/d, 1-r/d`. -/
abbrev proposal (d n : ℤ) := PSRNPowerUniform.model d n.toNat

abbrev proposalRepresentation (d n : ℤ) := PSRNPowerUniform.representation d n.toNat

abbrev BetaState (r d : ℤ) :=
  Option (Conditioning.Accepted (PSRNJohnkBeta.ratio (proposal d r) (proposal d (d - r))
    (proposalRepresentation d r) (proposalRepresentation d (d - r))) ([], [])
    (PSRNJohnkBeta.accepted (proposal d r) (proposal d (d - r))))

section mathematics

open MeasureTheory ProbabilityTheory

theorem proposal_law {d n : ℤ} (hn : 0 < n) (hd : 0 < d) :
    (proposal d n).law [] = betaMeasure ((n : ℝ) / d) 1 := by
  have hn' : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn.le
  rw [proposal, PSRNPowerUniform.initial_law d (by omega), hn',
    ← PSRNPowerUniformBeta.map_rpow_inv _ (div_pos (by exact_mod_cast hn) (by exact_mod_cast hd)),
    inv_div]

theorem proposal_measurableError (d n : ℤ) (hd : 0 < d) :
    (proposal d n).MeasurableError := by
  unfold proposal PSRNPowerUniform.model
  rw [PSRNPowerUniform.stage_pos _ hd]
  by_cases h1 : n.toNat = 1
  · rw [h1, PSRNPowerUniform.rooted_one]
    exact IntegerPower.measurableError _ (fun _ => measurable_const) _
  · rw [PSRNPowerUniform.rooted_root _ h1]
    exact Model.MeasurableError.nthRoot _ _

private theorem shapes {r d : ℤ} (h : 0 < r ∧ r < d) :
    0 < (r : ℝ) / d ∧ 0 < ((d - r : ℤ) : ℝ) / d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast h.1.trans h.2
  exact ⟨div_pos (by exact_mod_cast h.1) hd, div_pos (by exact_mod_cast sub_pos.mpr h.2) hd⟩

theorem acceptance_ne_zero {r d : ℤ} (h : 0 < r ∧ r < d) :
    ProductModel.posterior (proposal d r) (proposal d (d - r)) ([], [])
      (PSRNJohnkBeta.accepted (proposal d r) (proposal d (d - r))) ≠ 0 :=
  PSRNJohnkBeta.acceptance_ne_zero (shapes h).1 (shapes h).2
    (proposal_law h.1 (h.1.trans h.2)) (proposal_law (by omega) (h.1.trans h.2))

end mathematics

/-- Outside the subunit domain the beta factor is never constructed; this placeholder
only keeps the model total. -/
private def unusedBetaModel (r d : ℤ) : Model (ℝ × ℝ) (BetaState r d) where
  posterior _ := ProductModel.posterior (proposal d r) (proposal d (d - r)) ([], [])
  probability _ := inferInstance
  value := (PSRNJohnkBeta.ratio (proposal d r) (proposal d (d - r))
    (proposalRepresentation d r) (proposalRepresentation d (d - r))).value
  measurable_value := (PSRNJohnkBeta.ratio _ _ _ _).measurable_value
  refines _ _ := True
  refines_refl _ := trivial
  refines_trans _ _ := trivial
  absolutelyContinuous _ := MeasureTheory.Measure.AbsolutelyContinuous.rfl
  error := (PSRNJohnkBeta.ratio (proposal d r) (proposal d (d - r))
    (proposalRepresentation d r) (proposalRepresentation d (d - r))).error
  error_tendsto _ := (PSRNJohnkBeta.ratio _ _ _ _).error_tendsto ([], [])

/-- The beta factor returned by the actual constructor with shapes `r/d, 1-r/d`. -/
def betaModel (r d : ℤ) : Model (ℝ × ℝ) (BetaState r d) :=
  if h : 0 < r ∧ r < d then
    PSRNJohnkBeta.model (proposal d r) (proposal d (d - r)) (proposalRepresentation d r)
      (proposalRepresentation d (d - r)) [] [] (acceptance_ne_zero h)
  else unusedBetaModel r d

/-! ## The returned sum -/

abbrev exponentialModel (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :=
  LatentExponential.model (rate a b) (PSRNRationalRateDecay.rate_pos a b ha hb)

abbrev IntegerWorld (sn sd : ℤ) :=
  LatentGammaInteger.World (ℕ × ℝ) (PSRNGammaInteger.depth (sn / sd))

abbrev IntegerState (sn sd a b : ℤ) :=
  LatentGammaInteger.State (LatentExponential.State (rate a b)) (PSRNGammaInteger.depth (sn / sd))

/-- Without a remainder only the integer part exists; otherwise it carries both factors. -/
abbrev World (sn sd : ℤ) : Bool → Type
  | false => IntegerWorld sn sd
  | true => IntegerWorld sn sd × ((ℝ × ℝ) × (ℕ × ℝ))

instance worldMeasurableSpace (sn sd : ℤ) : (b : Bool) → MeasurableSpace (World sn sd b)
  | false => inferInstanceAs (MeasurableSpace (IntegerWorld sn sd))
  | true => inferInstanceAs (MeasurableSpace (IntegerWorld sn sd × ((ℝ × ℝ) × (ℕ × ℝ))))

abbrev State (sn sd a b : ℤ) : Bool → Type
  | false => IntegerState sn sd a b
  | true => IntegerState sn sd a b × (BetaState (sn % sd) sd × LatentExponential.State (rate a b))

/-- Whether the source enters its fractional branch. -/
def fractional (sn sd : ℤ) : Bool := sn % sd != 0

def branchModel (sn sd a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (frac : Bool) → Model (World sn sd frac) (State sn sd a b frac)
  | false => integerModel (sn / sd) a b ha hb
  | true => LatentGammaFraction.model (integerModel (sn / sd) a b ha hb) (betaModel (sn % sd) sd)
      (exponentialModel a b ha hb)

def branchInitial (sn sd a b : ℤ) : (frac : Bool) → State sn sd a b frac
  | false => PSRNGammaInteger.initial (sn / sd) a b
  | true => (PSRNGammaInteger.initial (sn / sd) a b, none, LatentExponential.initial (rate a b))

/-- The returned gamma draw over the source's actual branch. -/
abbrev model (sn sd a b : ℤ) (ha : 0 < a) (hb : 0 < b) :=
  branchModel sn sd a b ha hb (fractional sn sd)

abbrev initial (sn sd a b : ℤ) := branchInitial sn sd a b (fractional sn sd)

section mathematics

open MeasureTheory ProbabilityTheory

/-- The integer part has the Erlang law of its shape, including the zero shape. -/
theorem integer_law (w a b : ℤ) (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) :
    (integerModel w a b ha hb).law (PSRNGammaInteger.initial w a b) =
      GammaErlang.law (rate a b) w.toNat := by
  unfold integerModel
  split_ifs with h0
  · subst w
    simp [Model.law, Model.constant, Measure.map_const]
  · have hw' : 0 < w := lt_of_le_of_ne hw (Ne.symm h0)
    rw [PSRNGammaInteger.model_law w a b hw' ha hb, GammaErlang.law_eq_gamma _ _ (by omega)]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg hw).symm

theorem beta_law {r d : ℤ} (h : 0 < r ∧ r < d) :
    (betaModel r d).law none = betaMeasure ((r : ℝ) / d) (1 - (r : ℝ) / d) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (h.1.trans h.2).ne'
  have hshape : ((d - r : ℤ) : ℝ) / d = 1 - (r : ℝ) / d := by push_cast; field_simp
  rw [betaModel, dite_eq_left_of_eq_true (eq_true h), ← hshape]
  exact PSRNJohnkBeta.model_law (shapes h).1 (shapes h).2 (proposal_law h.1 (h.1.trans h.2))
    (proposal_law (by omega) (h.1.trans h.2)) _ _ _

/-- Every positive rational shape and rate gives the canonical gamma law. -/
theorem model_law (sn sd a b : ℤ) (hsn : 0 < sn) (hsd : 0 < sd) (ha : 0 < a) (hb : 0 < b) :
    (model sn sd a b ha hb).law (initial sn sd a b) =
      gammaMeasure ((sn : ℝ) / sd) (rate a b) := by
  have hdiv := Int.ediv_mul_add_emod sn sd
  have hw : 0 ≤ sn / sd := Int.ediv_nonneg hsn.le hsd.le
  have hsd' : (sd : ℝ) ≠ 0 := by exact_mod_cast hsd.ne'
  have hcast : ((sn / sd).toNat : ℝ) = ((sn / sd : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hw
  unfold model initial
  cases hf : fractional sn sd
  · have hr : sn % sd = 0 := by simpa [fractional] using hf
    have hpos : 0 < sn / sd := by
      rcases hw.lt_or_eq with h | h
      · exact h
      · rw [← h, hr] at hdiv; omega
    rw [branchModel, branchInitial, integer_law _ a b hw ha hb,
      GammaErlang.law_eq_gamma _ _ (by omega), hcast]
    congr 1
    rw [eq_div_iff hsd']
    exact_mod_cast (by rw [hr] at hdiv; linarith : sn / sd * sd = sn)
  · have hr : sn % sd ≠ 0 := by simpa [fractional] using hf
    have hrd : 0 < sn % sd ∧ sn % sd < sd :=
      ⟨lt_of_le_of_ne (Int.emod_nonneg _ hsd.ne') (Ne.symm hr), Int.emod_lt_of_pos _ hsd⟩
    rw [branchModel, branchInitial, LatentGammaFraction.model_law _ _ _ _ _ _
      ((sn % sd : ℤ) / (sd : ℝ)) (rate a b) (sn / sd).toNat (shapes hrd).1
      (by rw [div_lt_one (by exact_mod_cast hsd)]; exact_mod_cast hrd.2)
      (PSRNRationalRateDecay.rate_pos a b ha hb) (integer_law _ a b hw ha hb) (beta_law hrd)
      (LatentExponential.initial_law _ _), hcast]
    congr 1
    rw [eq_div_iff hsd', add_mul, div_mul_cancel₀ _ hsd']
    exact_mod_cast (by linarith : sn % sd + sn / sd * sd = sn)

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A zero integer part is the returned constant closure; otherwise the gamma oracle. -/
def integerOwns (w a b : ℤ) :
    Val rT → LatentGammaInteger.State (LatentExponential.State (rate a b))
      (PSRNGammaInteger.depth w) → IProp GF :=
  if w = 0 then ViewOwns (LatentRational.value 0 1) (fun _ => iprop(emp))
  else PSRNGammaInteger.owns w a b

/-- The integer part, for every integer quotient of positive parameters. -/
theorem integer_latentDistSpec (E : CoPset) (w a b : ℤ) (hw : 0 ≤ w) (ha : 0 < a)
    (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E (Program.integer w a b) (integerModel w a b ha hb)
      (PSRNGammaInteger.initial w a b) (integerOwns w a b) := by
  unfold integerModel integerOwns
  split_ifs with h0
  · subst w
    refine ⟨(represented_constant_viewSpec E _ (fun _ => iprop(emp)) 0 1 one_pos).forget,
      fun F hF => ?_⟩
    iintro Hcredit
    iapply Program.twp_integer_zero
    twp_pures
    twp_value
    imodintro
    iexists PSRNGammaInteger.initial 0 a b
    isplit
    · ipureintro
      exact Model.refines_refl _ _
    isimp only [ViewOwns]
    iframe Hcredit
    isplit
    · ipureintro
      rfl
    itrivial
  · have hspec := PSRNGammaInteger.newGammaInteger_latentDistSpec (rT := rT) (GF := GF) E w a b
      (lt_of_le_of_ne hw (Ne.symm h0)) ha hb
    refine ⟨hspec.oracle, fun F hF => ?_⟩
    iintro Hcredit
    iapply Program.twp_integer_pos E w a b h0
    iapply hspec.spec F hF $$ Hcredit

/-- The beta factor retains both of Johnk's proposal caches. -/
abbrev betaOwns (r d : ℤ) : Val rT → BetaState r d → IProp GF :=
  PSRNJohnkBeta.owns (proposalRepresentation d r) (proposalRepresentation d (d - r)) [] []
    (PSRNPowerUniform.owns d r.toNat) (PSRNPowerUniform.owns d (d - r).toNat)

private theorem proposal_spec (E : CoPset) (d n : ℤ) (hn : 0 < n) :
    IsRepresentedDistSpec (GF := GF) E pl(&Occil.PSRN.newPowerUniform #d #n #())
      (proposal d n) (proposalRepresentation d n) [] (PSRNPowerUniform.owns d n.toNat) := by
  have h := PSRNPowerUniform.newPowerUniform_representedDistSpec (rT := rT) (GF := GF) E d
    n.toNat (by omega)
  rwa [Int.toNat_of_nonneg hn.le] at h

/-- The actual beta constructor with complementary subunit shapes `r/d, 1-r/d`. -/
theorem beta_latentDistSpec (E : CoPset) (r d : ℤ) (h : 0 < r ∧ r < d) :
    IsLatentDistSpec (GF := GF) E (Program.beta r d) (betaModel r d) none (betaOwns r d) := by
  have hd : 0 < d := h.1.trans h.2
  rw [betaModel, dite_eq_left_of_eq_true (eq_true h)]
  exact PSRNJohnkBeta.newBeta_latentDistSpec E r d (d - r) d h.1 h.2 (by omega) (by omega)
    (shapes h).1 (shapes h).2 _ _ [] [] _ _ (proposal_spec E d r h.1)
    (proposal_spec E d (d - r) (by omega)) (proposal_measurableError d r hd)
    (proposal_measurableError d (d - r) hd) (proposal_law h.1 hd) (proposal_law (by omega) hd)

def branchOwns (sn sd a b : ℤ) :
    (frac : Bool) → Val rT → State sn sd a b frac → IProp GF
  | false => integerOwns (sn / sd) a b
  | true => Core.owns (integerOwns (sn / sd) a b) (betaOwns (sn % sd) sd)
      (PSRNExponential.rationalOwns a b)

/-- The returned closure owns the integer part and, with a remainder, both factors. -/
abbrev owns (sn sd a b : ℤ) := branchOwns (rT := rT) (GF := GF) sn sd a b (fractional sn sd)

/-- Every positive rational shape and rate: construction and all later observations of the
returned gamma draw retain the joint world of its integer, beta and exponential parts. -/
theorem newGamma_latentDistSpec (E : CoPset) (sn sd a b : ℤ) (hsn : 0 < sn) (hsd : 0 < sd)
    (ha : 0 < a) (hb : 0 < b) :
    IsLatentDistSpec (GF := GF) E pl(&Occil.PSRN.newGamma #sn #sd #a #b #())
      (model sn sd a b ha hb) (initial sn sd a b) (owns sn sd a b) := by
  have hw : 0 ≤ sn / sd := Int.ediv_nonneg hsn.le hsd.le
  have hI := integer_latentDistSpec (rT := rT) (GF := GF) E (sn / sd) a b hw ha hb
  unfold model initial owns
  cases hf : fractional sn sd
  · have hr : sn % sd = 0 := by simpa [fractional] using hf
    change IsLatentDistSpec E _ (integerModel (sn / sd) a b ha hb)
      (PSRNGammaInteger.initial (sn / sd) a b) (integerOwns (sn / sd) a b)
    refine ⟨hI.oracle, fun F hF => ?_⟩
    iintro Hcredit
    iapply Program.twp_open E sn sd a b hsn hsd ha hb
    rw [hr]
    unfold Program.bind
    twp_bind (Program.integer (sn / sd) a b)
    iapply hI.wp F hF _ $$ Hcredit
    iintro %v %t %ht Hstate Hcredit
    ieval (change _ ⊢ tglWp E (Program.bind (.ofVal v) (Program.remainderTest 0 sd a b)) _)
    iapply Program.twp_remainder_zero
    iexists t
    iframe Hstate Hcredit
    ipureintro
    exact ht
  · have hr : sn % sd ≠ 0 := by simpa [fractional] using hf
    have hrd : 0 < sn % sd ∧ sn % sd < sd :=
      ⟨lt_of_le_of_ne (Int.emod_nonneg _ hsd.ne') (Ne.symm hr), Int.emod_lt_of_pos _ hsd⟩
    have hB := beta_latentDistSpec (rT := rT) (GF := GF) E (sn % sd) sd hrd
    have hE := PSRNExponential.newExponential_latentDistSpec (rT := rT) (GF := GF) E a b ha hb
    let I := integerModel (sn / sd) a b ha hb
    let D := LatentGammaFraction.model I (betaModel (sn % sd) sd) (exponentialModel a b ha hb)
    let i := PSRNGammaInteger.initial (sn / sd) a b
    let jk := ((none : BetaState (sn % sd) sd), LatentExponential.initial (rate a b))
    change IsLatentDistSpec E _ D (i, jk) _
    refine ⟨Core.oracleSpec E _ _ _ _ _ _ hI.oracle hB.oracle hE.oracle, fun F hF => ?_⟩
    iintro Hcredit
    iapply Program.twp_open E sn sd a b hsn hsd ha hb
    unfold Program.bind
    twp_bind (Program.integer (sn / sd) a b)
    -- The integer part first, with the fractional factors' credit integrated out.
    let C := LatentGammaFraction.fraction (betaModel (sn % sd) sd) (exponentialModel a b ha hb)
    have hsplit (u : IntegerState sn sd a b) :
        ∫⁻ x, ProductModel.leftCredit C jk F x ∂I.posterior u = ∫⁻ x, F x ∂D.posterior (u, jk) :=
      (ProductModel.expectation_left I C (u, jk) F hF).symm
    ihave Hcredit := ErrorCredit.weaken (hsplit i).le $$ Hcredit
    iapply hI.wp _ (ProductModel.measurable_leftCredit C jk hF) _ $$ Hcredit
    iintro %iv %s %hs HI Hcredit
    ihave Hcredit := ErrorCredit.weaken (hsplit s).ge $$ Hcredit
    ieval (change _ ⊢ tglWp E (Program.bind (.ofVal iv)
      (Program.remainderTest (sn % sd) sd a b)) _)
    iapply Program.twp_remainder_pos E _ sd a b hr iv
    iapply Core.twp_fraction E (sn % sd) sd a b I _ _ i none _ _ _ _ hB hE iv s hs F hF
    iframe HI Hcredit

end specification

end

end SampLib.PSRNGamma
