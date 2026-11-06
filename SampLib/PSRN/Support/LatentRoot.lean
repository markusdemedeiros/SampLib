import SampLib.PSRN.Support.LatentRepresentedSpec
import SampLib.PSRN.Laws.FloorUncertainty
import SampLib.PSRN.Support.PSRNRoot

/-! # Compositional constructor and observer specifications for deferred roots -/

open MeasureTheory Filter Topology

namespace SampLib.LatentReal

noncomputable section

/-- The closed dyadic cell selected by the real floor convention. -/
def dyadicInterval (n : ℕ) (x : ℝ) : RationalInterval :=
  let lo := ⌊x * (((2 : ℤ) ^ n : ℤ) : ℝ)⌋
  ⟨lo, lo + 1, (2 : ℤ) ^ n, by positivity, by omega⟩

theorem dyadicInterval_contains (n : ℕ) (x : ℝ) : (dyadicInterval n x).Contains x := by
  have hd : (0 : ℝ) < (((2 : ℤ) ^ n : ℤ) : ℝ) := by positivity
  constructor
  · exact (div_le_iff₀ hd).mpr (Int.floor_le _)
  · apply (le_div_iff₀ hd).mpr
    simpa only [dyadicInterval, Int.cast_add, Int.cast_one] using
      (Int.lt_floor_add_one (x * (((2 : ℤ) ^ n : ℤ) : ℝ))).le

@[simp] theorem dyadicInterval_width (n : ℕ) (x : ℝ) :
    (dyadicInterval n x).width = (1 / 2 : ℝ) ^ n := by
  calc
    _ = 1 / (((2 : ℤ) ^ n : ℤ) : ℝ) := by
      dsimp [RationalInterval.width, RationalInterval.lowerReal, RationalInterval.upperReal,
        dyadicInterval]
      push_cast
      ring
    _ = _ := by simp

theorem dyadicInterval_approximates (x : ℝ) :
    RationalInterval.Approximates (fun n => dyadicInterval n x) x := by
  refine ⟨fun n => dyadicInterval_contains n x, ?_⟩
  simp_rw [dyadicInterval_width]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

variable {Ω S : Type} [MeasurableSpace Ω]

/-- Every real projection has a canonical measurable dyadic floor-cell schedule. -/
def Model.dyadicRepresentation (D : Model Ω S) : Representation D where
  interval n x := dyadicInterval n (D.value x)
  measurable_lower _n := (D.measurable_value.mul_const _).floor
  measurable_upper _n := ((D.measurable_value.mul_const _).floor).add_const 1
  measurable_denominator _ := measurable_const
  approximates _ := ae_of_all _ fun x => dyadicInterval_approximates (D.value x)

/-- Exact endpoint-format facts identify the represented interval without another program proof. -/
theorem Model.observed_dyadic_of_format (D : Model Ω S) (s : S) (n : ℕ) (I : RationalInterval)
    (hdenominator : I.denominator = (2 : ℤ) ^ n) (hgap : I.upper = I.lower + 1)
    (hfloor : ∀ᵐ x ∂D.posterior s, ⌊D.value x * (((2 : ℤ) ^ n : ℤ) : ℝ)⌋ = I.lower) :
    D.dyadicRepresentation.Observed s n I := by
  filter_upwards [hfloor] with x hx
  change I = dyadicInterval n (D.value x)
  cases I with
  | mk lo hi denominator hpos hordered =>
    dsimp only at hdenominator hgap hx
    subst hi
    subst denominator
    simp only [dyadicInterval, hx]

end

end SampLib.LatentReal

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.Root

noncomputable section

private instance root_closed {rT : Type} : ClosedExp (Occil.PSRN.root : Exp rT) where
  lc := by is_lc
  fv := by kernel_rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- The root closure retains its actual source and its current comparison domain. -/
def owns (D : Model Ω S) (degree : ℕ) (rawOwns : Val rT → S → IProp GF)
    (v : Val rT) (s : S) : IProp GF :=
  iprop(∃ source : Val rT, ⌜v = Program.value source degree ∧ Admissible D degree s⌝ ∗
    rawOwns source s)

/-- Every observation refines the same source and preserves all joint latent credit. -/
theorem representedOracleSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (rawOwns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsRepresentedOracleSpec E (D.nthRoot degree) (D.nthRoot degree).dyadicRepresentation
      (owns D degree rawOwns) where
  observe v s n F hF := by
    iintro ⟨Hstate, Hcredit⟩
    isimp only [owns] at Hstate
    icases Hstate with ⟨%source, %hv, Hstate⟩
    rcases hv with ⟨rfl, hadmissible⟩
    isimp only [Model.nthRoot] at Hcredit
    iapply tglWp_wand
    isplitl [Hstate Hcredit]
    · iapply twp_observe E D hD (rawOwns source) source
        (hsource.viewSpec E D rawOwns source) degree hdegree s hadmissible n F hF
      iframe Hstate Hcredit
    iintro %result ⟨%t, %I, %hI, Hstate, Hcredit⟩
    iexists t, I
    isplit
    · ipureintro
      exact ⟨hI.1, hI.2.1, hI.2.2.1,
        (D.nthRoot degree).observed_dyadic_of_format t n I
          hI.2.2.2.1 hI.2.2.2.2.1
          (by simpa only [Model.nthRoot, Int.cast_pow] using hI.2.2.2.2.2)⟩
    isplitl [Hstate]
    · isimp only [owns]
      iexists source
      iframe Hstate
      ipureintro
      exact ⟨rfl, hadmissible.refines hI.2.1⟩
    isimp only [Model.nthRoot]
    iframe Hcredit

/-- Forgetting endpoint format gives the ordinary shared-oracle protocol. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (hD : D.MeasurableError)
    (rawOwns : Val rT → S → IProp GF) (hsource : IsOracleSpec E D rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) :
    IsOracleSpec E (D.nthRoot degree) (owns D degree rawOwns) :=
  (representedOracleSpec E D hD rawOwns hsource degree hdegree).forget

/-- The actual constructor composes with an admissible source sampler. -/
theorem latentDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S) (hD : D.MeasurableError)
    (initial : S) (rawOwns : Val rT → S → IProp GF)
    (hsource : IsLatentDistSpec E e D initial rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) (hadmissible : Admissible D degree initial) :
    IsLatentDistSpec E pl(let source := &e; &Occil.PSRN.root source #int (degree : ℤ))
      (D.nthRoot degree) initial (owns D degree rawOwns) where
  oracle := oracleSpec E D hD rawOwns hsource.oracle degree hdegree
  spec F hF := by
    iintro Hcredit
    isimp only [Model.nthRoot] at Hcredit
    twp_bind e
    iapply hsource.wp F hF _ $$ Hcredit
    iintro %source %t %ht Hstate Hcredit
    twp_pure
    isimp only [ClosedExp.openRec, ClosedExp.closeRec]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply Program.twp_root E source degree hdegree (rawOwns source) t $$ Hstate
    iintro %v Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    subst v
    iexists t
    isplit
    · ipureintro
      exact ht
    isplitl [Hstate]
    · isimp only [owns]
      iexists source
      iframe Hstate
      ipureintro
      exact ⟨rfl, hadmissible.refines ht⟩
    isimp only [Model.nthRoot]
    iframe Hcredit

/-- The constructor also provides its exact, reusable dyadic interval representation. -/
theorem representedDistSpec (E : CoPset) (e : Exp rT) (D : Model Ω S)
    (hD : D.MeasurableError) (initial : S) (rawOwns : Val rT → S → IProp GF)
    (hsource : IsLatentDistSpec E e D initial rawOwns)
    (degree : ℕ) (hdegree : 2 ≤ degree) (hadmissible : Admissible D degree initial) :
    IsRepresentedDistSpec E pl(let source := &e; &Occil.PSRN.root source #int (degree : ℤ))
      (D.nthRoot degree) (D.nthRoot degree).dyadicRepresentation initial
      (owns D degree rawOwns) where
  spec := (latentDistSpec E e D hD initial rawOwns hsource degree hdegree hadmissible).spec
  oracle := representedOracleSpec E D hD rawOwns hsource.oracle degree hdegree

end specification

end

end SampLib.LatentReal.Root
