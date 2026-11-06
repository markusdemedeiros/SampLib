import SampLib.Discrete.Zipf

open ProbLang
open scoped ENNReal

namespace ReviewExactDiscrete005

noncomputable section

open SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem framed (E : CoPset) (n a b : ℕ) [NeZero n] (hb : 0 < b)
    (F : Fin n → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ k, F k ∂Zipf.law n a b hb) ∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.zipf #int (n : ℤ) #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ k : Fin n, ⌜v = Val.int (k + 1 : ℕ)⌝ ∗ ↯ (F k) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((Zipf.zipf_distSpec E n a b hb).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %k Hcredit
  iexists k
  iframe Hcredit HR
  itrivial

example (E : CoPset) (R : IProp GF) := framed E 4 0 7 (by decide) (fun _ => ∞) R
example (E : CoPset) (R : IProp GF) := framed E 1 9 2 (by decide) (fun _ => ∞) R
example (E : CoPset) (F : Fin 3 → ℝ≥0∞) (R : IProp GF) :=
  framed E 3 2 3 (by decide) F R

end

open SampLib

example : Zipf.law 4 0 7 (by decide) {(2 : Fin 4)} = (4 : ℝ≥0∞)⁻¹ := by
  rw [Zipf.law_zero, UniformFin.law_singleton]
  norm_num

example : Zipf.law 1 9 2 (by decide) {(0 : Fin 1)} = 1 := by
  rw [Zipf.law_one]
  simp

example (n a b : ℕ) [NeZero n] (hb : 0 < b) (k : Fin n) :
    Zipf.law n a b hb {k} =
      ENNReal.ofReal (((k : ℕ) + 1 : ℝ) ^ (-((a : ℝ) / b))) /
        ∑ j : Fin n, ENNReal.ofReal (((j : ℕ) + 1 : ℝ) ^ (-((a : ℝ) / b))) := by
  rw [Zipf.law_singleton]
  simp only [Zipf.normalizer, Zipf.weight_eq]

#print axioms SampLib.Zipf.zipf_distSpec
#print axioms SampLib.Zipf.expectation
#print axioms SampLib.Zipf.law_singleton
#print axioms framed

end ReviewExactDiscrete005
