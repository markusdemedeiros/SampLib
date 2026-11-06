import SampLib.Samplers.DecreasingTrial
import SampLib.Samplers.Exponential
import SampLib.Samplers.Laplace
import SampLib.Samplers.Erlang
import Metrology.Iris.LocalBI

/-! Independent continuous-sampler boundary, infinity, and resource checks. -/

open ProbLang
open scoped ENNReal

namespace NextBatchContinuousReview

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS SampLib

variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS ℝ hlc GF]
  [ProbLangDist ℝ] [ProbLangDist.IsUniformReal ℝ] [ProbLangFFI ℝ] [ProbLangObs ℝ]
local bi (IProp GF)

example (E : CoPset) (F : ℕ → ℝ≥0∞) (n : ℕ) :
    ⊢ ↯ (DecreasingTrial.credit F n 0) -∗
      tglWp E pl(&Occil.decreasingTrial #int (n : ℤ) #real (0 : ℝ))
        (fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (F k))) :=
  DecreasingTrial.twp_decreasingTrial E F n 0 (by norm_num)

example (E : CoPset) (n : ℕ) :
    ⊢ ↯ (DecreasingTrial.credit (fun _ => ∞) n 1) -∗
      tglWp E pl(&Occil.decreasingTrial #int (n : ℤ) #real (1 : ℝ))
        (fun v : Val ℝ => iprop(∃ k : ℕ, ⌜v = Val.int k⌝ ∗ ↯ (∞ : ℝ≥0∞))) :=
  DecreasingTrial.twp_decreasingTrial E (fun _ => ∞) n 1 (by norm_num)

section framed
variable [ProbLangDist.IsUniformInt ℝ]

example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂Exponential.law) ∗ I -∗
      tglWp E pl(&Occil.exponential #())
        (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((Exponential.exponential_distSpec E).wp F hF _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HI
  itrivial

example (E : CoPset) (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂Laplace.law) ∗ I -∗
      tglWp E pl(&Occil.laplace #())
        (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((Laplace.laplace_distSpec E).wp F hF _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HI
  itrivial

example (E : CoPset) (shape : ℕ) (hshape : 0 < shape)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (I : IProp GF) :
    ⊢ ↯ (∫⁻ z, F z ∂Erlang.law (shape - 1)) ∗ I -∗
      tglWp E pl(&Occil.erlang #int (shape : ℤ))
        (fun v : Val ℝ => iprop(∃ z : ℝ, ⌜v = Val.real z⌝ ∗ ↯ (F z) ∗ I)) := by
  iintro ⟨Hcredit, HI⟩
  iapply ((Erlang.erlang_distSpec E shape hshape).wp F hF _) $$ Hcredit
  iintro %z Hcredit
  iexists z
  iframe Hcredit HI
  itrivial

end framed

example : (∫⁻ _ : ℝ, (∞ : ℝ≥0∞) ∂Exponential.law) = ∞ := by simp
example : (∫⁻ _ : ℝ, (∞ : ℝ≥0∞) ∂Laplace.law) = ∞ := by simp
example (n : ℕ) : (∫⁻ _ : ℝ, (∞ : ℝ≥0∞) ∂Erlang.law n) = ∞ := by simp
example : Erlang.law 0 = ProbabilityTheory.expMeasure 1 := Erlang.law_zero

example (E : CoPset) :
    IsDistSpec (GF := GF) E pl(&Occil.erlang #int (1 : ℤ)) (Erlang.law 0) Val.real := by
  simpa using Erlang.erlang_distSpec E 1 (by norm_num)

example : Laplace.law.map (fun x => -x) = Laplace.law := Laplace.map_neg

#print axioms SampLib.Distributions.Exponential.lintegral_expMeasure
#print axioms SampLib.DecreasingTrial.twp_decreasingTrial
#print axioms SampLib.Exponential.exponential_distSpec
#print axioms SampLib.Laplace.laplace_distSpec
#print axioms SampLib.Erlang.erlang_distSpec

end

end NextBatchContinuousReview
