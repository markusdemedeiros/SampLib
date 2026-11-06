import SampLib.PSRN.Support.LatentRepresentedCoordinateSum

open ProbLang
open scoped ENNReal

namespace RepresentedCoordinateSumCallers

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib.LatentReal

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω S : Type} [MeasurableSpace Ω]
local bi (IProp GF)

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (handle : Val rT) (h : IsRepresentedViewSpec E D R P handle) :
    IsRepresentedViewSpec E
      (CoordinateSum.model D (fun _ : Fin 2 => D) (fun _ => .refl D))
      (CoordinateSum.representation D (fun _ : Fin 2 => D) (fun _ => .refl D) (fun _ => R)) P
      (CoordinateSum.value (fun _ : Fin 2 => handle)) :=
  CoordinateSum.represented_oracleSpec E D _ _ _ _ P (fun _ => h)

example (E : CoPset) (D : Model Ω S) (P : S → IProp GF) :
    IsRepresentedViewSpec E (D.constant 0)
      (Representation.point D 0 0 1 (by decide) (by norm_num)) P
      (SampLib.LatentRational.value 0 1 : Val rT) :=
  represented_point_viewSpec E D P 0 0 1 (by decide) (by norm_num)

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (handle : Val rT) (h : IsRepresentedViewSpec E D R P handle)
    (s : S) (n : ℕ) (F : Ω → ℝ≥0∞) (hF : Measurable F) (Φ : Val rT → IProp GF) :=
  IsRepresentedViewSpec.wp h s n F hF Φ

example (E : CoPset) (D : Model Ω S) (R : Representation D) (P : S → IProp GF)
    (handle : Val rT) (h : IsRepresentedViewSpec E D R P handle)
    (s : S) (n : ℕ) (Φ : Val rT → IProp GF) :=
  IsRepresentedViewSpec.wp h s n (fun _ => ∞) measurable_const Φ

#print axioms IsRepresentedViewSpec.wp
#print axioms Representation.add
#print axioms Representation.observed_add
#print axioms represented_point_viewSpec
#print axioms represented_add_oracleSpec
#print axioms CoordinateSum.represented_oracleSpec

end

end RepresentedCoordinateSumCallers
