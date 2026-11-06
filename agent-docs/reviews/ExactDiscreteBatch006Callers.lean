import SampLib.Samplers.Zeta
import SampLib.Samplers.PolyaRational

open ProbLang
open scoped ENNReal

namespace ReviewExactDiscrete006

noncomputable section

open SampLib Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

theorem zeta_framed (E : CoPset) (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ n, F n ∂Zeta.law a b hb hab) ∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.zeta #int (a : ℤ) #int (b : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((Zeta.zeta_distSpec E a b hb hab).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iexists n
  iframe Hcredit HR
  itrivial

theorem polya_framed (E : CoPset) (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s)
    (hst : s ≤ t) (F : ℕ → ℝ≥0∞) (R : IProp GF) :
    ⊢ ↯ (∫⁻ n, F n ∂PolyaRational.law A B s t hA hB hs hst) ∗ R -∗
      tglWp E pl(&Occil.DiscreteExtra.polyaRational
        #int (A : ℤ) #int (B : ℤ) #int (s : ℤ) #int (t : ℤ))
        (fun v : Val rT => iprop(∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n) ∗ R)) := by
  iintro ⟨Hcredit, HR⟩
  iapply ((PolyaRational.polyaRational_distSpec E A B s t hA hB hs hst).wp F
    (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iexists n
  iframe Hcredit HR
  itrivial

-- Zeta: smallest exponents above one, a non-integer exponent, and infinite credit.
example (E : CoPset) (R : IProp GF) := zeta_framed E 2 1 (by decide) (by decide) (fun _ => ∞) R
example (E : CoPset) (R : IProp GF) := zeta_framed E 3 2 (by decide) (by decide) (fun _ => ∞) R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  zeta_framed E 101 100 (by decide) (by decide) F R

-- Polya: certain success s = t, integer and fractional shapes, shape below one.
example (E : CoPset) (R : IProp GF) :=
  polya_framed E 1 1 1 1 (by decide) (by decide) (by decide) le_rfl (fun _ => ∞) R
example (E : CoPset) (R : IProp GF) :=
  polya_framed E 1 3 1 2 (by decide) (by decide) (by decide) (by decide) (fun _ => ∞) R
example (E : CoPset) (F : ℕ → ℝ≥0∞) (R : IProp GF) :=
  polya_framed E 7 2 3 5 (by decide) (by decide) (by decide) (by decide) F R

end

open SampLib

-- The zeta law is the normalized positive-integer power law.
example (a b : ℕ) (hb : 0 < b) (hab : b < a) : Zeta.law a b hb hab {0} = 0 :=
  Zeta.law_zero a b hb hab

example (a b : ℕ) (hb : 0 < b) (hab : b < a) (n : ℕ) :
    Zeta.law a b hb hab {n + 1} =
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ (-((a : ℝ) / b))) /
        ∑' m : ℕ, ENNReal.ofReal (((m + 1 : ℕ) : ℝ) ^ (-((a : ℝ) / b))) := by
  rw [Zeta.law_singleton]
  rfl

example (a b : ℕ) (hb : 0 < b) (hab : b < a) : Zeta.normalizer a b ≠ ∞ :=
  Zeta.normalizer_ne_top a b hb hab

-- The Polya law has the canonical real-shape negative-binomial mass.
example (A B s t : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hst : s ≤ t) (n : ℕ) :
    PolyaRational.law A B s t hA hB hs hst {n} =
      ENNReal.ofReal (Ring.multichoose ((A : ℝ) / B) n * ((s : ℝ) / t) ^ ((A : ℝ) / B) *
        (1 - (s : ℝ) / t) ^ n) := by
  rw [NegativeBinomialShape.law_singleton]
  simp [NegativeBinomialShape.pmf, PolyaRational.shape, PolyaRational.success,
    RationalCoin.bias]

-- At s = t every trial succeeds and the count is zero.
example (A B s : ℕ) (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) :
    PolyaRational.law A B s s hA hB hs le_rfl = MeasureTheory.Measure.dirac 0 := by
  have h1 : PolyaRational.success s s hs le_rfl = 1 := by
    apply Subtype.ext
    simp [PolyaRational.success, RationalCoin.bias, hs.ne']
  simp only [PolyaRational.law, h1]
  exact NegativeBinomialShape.law_one _ _

#print axioms SampLib.Zeta.zeta_distSpec
#print axioms SampLib.Zeta.law_singleton
#print axioms SampLib.PolyaRational.polyaRational_distSpec
#print axioms zeta_framed
#print axioms polya_framed

end ReviewExactDiscrete006
