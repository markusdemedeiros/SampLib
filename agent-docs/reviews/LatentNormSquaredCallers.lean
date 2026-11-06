import SampLib.LatentNormSquared
import SampLib.LatentNormSquaredLaw

open ProbLang SampLib.LatentReal SampLib.LatentReal.NormSquared
open scoped ENNReal

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (D : Model Ω S) (x : Ω) :
    (model D (fun _ : Fin 2 => D) (fun _ => .refl D)).value x = 2 * D.value x ^ 2 := by
  rw [value_eq]
  simp

example (E : CoPset) (D : Model Ω S) (handle : Val rT) (P : S → IProp GF)
    (h : IsViewSpec E D P handle) :
    IsViewSpec E (model D (fun _ : Fin 2 => D) (fun _ => .refl D)) P
      (value (fun _ : Fin 2 => handle)) :=
  oracleSpec E D (fun _ : Fin 2 => D) (fun _ => .refl D)
    (fun _ : Fin 2 => handle) P (fun _ => h)

/-- Construction plus an actual observation, with arbitrary correlation and credit. -/
example (E : CoPset) (D : Model Ω S) {d : ℕ} (views : Fin d → Model Ω S)
    (hviews : ∀ i, D.SameWorld (views i)) (handles : Fin d → Val rT)
    (P : S → IProp GF) (hspec : ∀ i, IsViewSpec E (views i) P (handles i))
    (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) (R : IProp GF) :
    ⊢ P s ∗ R ∗ ↯ (∫⁻ x, F x ∂(model D views hviews).posterior s) -∗
      tglWp E pl(let norm := &Occil.PSRN.normSquared &(vectorVal handles).fst;
        norm #int (n : ℤ))
        (fun result : Val rT => iprop(∃ (t : S) (I : RationalInterval),
          ⌜result = intervalVal I ∧ (model D views hviews).Encloses t n I⌝ ∗
          P t ∗ R ∗ ↯ (∫⁻ x, F x ∂(model D views hviews).posterior t))) := by
  iintro ⟨Hstate, HR, Hcredit⟩
  twp_bind pl(&Occil.PSRN.normSquared &(vectorVal handles).fst)
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_normSquared E handles P s $$ Hstate
  iintro %norm Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hnorm, Hstate⟩
  subst norm
  twp_pure
  iapply (oracleSpec E D views hviews handles P hspec).wp s n F hF _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  iexists t, I
  iframe Hstate HR Hcredit
  ipureintro
  exact ⟨rfl, hI.2⟩

#print axioms SampLib.LatentReal.NormSquared.twp_normSquared
#print axioms SampLib.LatentReal.NormSquared.oracleSpec
#print axioms SampLib.LatentReal.NormSquared.law_eq
