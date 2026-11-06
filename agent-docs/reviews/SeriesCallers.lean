import SampLib.Samplers.Zeta
import SampLib.Samplers.RecycledSamples
import SampLib.Samplers.PolyaRational

/-! Owner-side caller checks for the `series` team: framed resources, domain boundaries,
infinite credits, and transitive axioms. -/

open ProbLang SampLib
open scoped ENNReal

#print axioms SampLib.Zeta.zeta_distSpec
#print axioms SampLib.PolyaRational.polyaRational_distSpec
#print axioms SampLib.RecycledUniform.twp_recycledUniform
#print axioms SampLib.RecycledUniform.recycledUniform_ownedDistSpec
#print axioms SampLib.RecycledSamples.recycledSamples_distSpec
#print axioms SampLib.RecycledSamples.recycledSamples_zero_distSpec

section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- Zeta at the boundary exponent `a/b = 2/1`, with an arbitrary framed resource. -/
example (E : CoPset) (R : IProp GF) (F : ℕ → ℝ≥0∞) :
    ⊢ R -∗ ↯ (∫⁻ n, F n ∂Zeta.law 2 1 (by norm_num) (by norm_num)) -∗
      tglWp E pl(&Occil.DiscreteExtra.zeta #int (2 : ℤ) #int (1 : ℤ))
        (fun v => iprop(R ∗ ∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro HR Hcredit
  iapply ((Zeta.zeta_distSpec (rT := rT) (GF := GF) E 2 1 one_pos one_lt_two).wp
    F (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iframe HR
  iexists n
  iframe Hcredit
  itrivial

/-- Zeta exponent just above one (`3/2`); zero output is paid by infinite credit. -/
example (E : CoPset) (R : IProp GF) :
    ⊢ R -∗ ↯ (∫⁻ n, (if n = 0 then ∞ else 0) ∂Zeta.law 3 2 (by norm_num) (by norm_num)) -∗
      tglWp E pl(&Occil.DiscreteExtra.zeta #int (3 : ℤ) #int (2 : ℤ))
        (fun v => iprop(R ∗ ∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗
          ↯ (if n = 0 then ∞ else 0))) := by
  iintro HR Hcredit
  iapply ((Zeta.zeta_distSpec (rT := rT) (GF := GF) E 3 2 two_pos (Nat.lt_succ_self 2)).wp
    _ (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iframe HR
  iexists n
  iframe Hcredit
  itrivial

/-- An arbitrary valid stored pool, with a framed resource and joint credits. -/
example (E : CoPset) (R : IProp GF) (pool : Loc) (n value width : ℕ) (hn : 0 < n)
    (hv : value < width) (F : EntropyPool.JointResult → ℝ≥0∞) :
    ⊢ R -∗ appHeapFrag pool (EntropyPool.poolVal (rT := rT) value width) -∗
      ↯ (∫⁻ z, F z ∂EntropyPool.recycledLaw n value width hn hv) -∗
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (n : ℤ))
        (fun v => iprop(R ∗ RecycledUniform.jointPost pool F v)) := by
  iintro HR Hpool Hcredit
  iapply tglWp_wand
  isplitl [Hpool Hcredit]
  · iapply RecycledUniform.twp_recycledUniform E pool n value width hn hv F
    iframe Hpool Hcredit
  iintro %v Hpost
  iframe HR Hpost

/-- Bound one from the reset pool: the output is `0` and the pool stays reset. -/
example (E : CoPset) (R : IProp GF) (pool : Loc) (F : ℕ → ℝ≥0∞) :
    ⊢ R -∗ appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1) -∗
      ↯ (∫⁻ r, F r ∂UniformInt.law 1) -∗
      tglWp E pl(&Occil.Weighted.recycledUniform #loc pool #int (1 : ℤ))
        (fun v => iprop(R ∗ ∃ r : ℕ, ⌜v = Val.int (r : ℤ)⌝ ∗
          appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1) ∗ ↯ (F r))) := by
  iintro HR Hpool Hcredit
  iapply ((RecycledUniform.recycledUniform_ownedDistSpec (rT := rT) (GF := GF) E pool 1).wp
    F (measurable_of_countable _) _) $$ Hpool Hcredit
  iintro %r Hpool Hcredit
  iframe HR
  iexists r
  iframe Hpool Hcredit
  itrivial

/-- Two reset-pool draws in sequence keep a framed resource; bound three needs fresh bits. -/
example (E : CoPset) (R : IProp GF) (pool : Loc) (F : ℕ → ℕ → ℝ≥0∞) :
    ⊢ R -∗ appHeapFrag pool (EntropyPool.poolVal (rT := rT) 0 1) -∗
      ↯ (∫⁻ r, ∫⁻ s, F r s ∂UniformInt.law 3 ∂UniformInt.law 3) -∗
      tglWp E pl(let x := &Occil.Weighted.recycledUniform #loc pool #int (3 : ℤ);
          let y := &Occil.Weighted.recycledUniform #loc pool #int (3 : ℤ); (x, y))
        (fun v => iprop(R ∗ ∃ r s : ℕ, ⌜v = Val.pair (Val.int (r : ℤ)) (Val.int (s : ℤ))⌝ ∗
          ↯ (F r s))) := by
  have h := RecycledUniform.recycledUniform_ownedDistSpec (rT := rT) (GF := GF) E pool 3
  iintro HR Hpool Hcredit
  twp_bind pl(&Occil.Weighted.recycledUniform #loc pool #int (3 : ℤ))
  iapply (h.wp (fun r => ∫⁻ s, F r s ∂UniformInt.law 3) (measurable_of_countable _) _)
    $$ Hpool Hcredit
  iintro %r Hpool Hcredit
  twp_pure
  twp_bind pl(&Occil.Weighted.recycledUniform #loc pool #int (3 : ℤ))
  iapply (h.wp (F r) (measurable_of_countable _) _) $$ Hpool Hcredit
  iintro %s - Hcredit
  twp_pures
  twp_value
  imodintro
  iframe HR
  iexists r, s
  iframe Hcredit
  itrivial

/-- Batches: zero count at bound one, and a nonpositive bound with zero count. -/
example (E : CoPset) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (∫⁻ xs, F xs ∂RecycledSamples.law 1 0) -∗
      tglWp E pl(&Occil.Weighted.recycledSamples #int (1 : ℤ) #int (0 : ℤ))
        (fun v => iprop(∃ xs : List ℕ,
          ⌜v = listVal (fun r : ℕ => (Val.int r : Val rT)) xs⌝ ∗ ↯ (F xs))) := by
  iintro Hcredit
  iapply ((RecycledSamples.recycledSamples_distSpec (GF := GF) E 1 0).spec F
    (measurable_of_countable _)) $$ Hcredit

example (E : CoPset) (F : List ℕ → ℝ≥0∞) :
    ⊢ ↯ (F []) -∗
      tglWp E pl(&Occil.Weighted.recycledSamples #int (-4 : ℤ) #int (0 : ℤ))
        (fun v => iprop(∃ xs : List ℕ,
          ⌜v = listVal (fun r : ℕ => (Val.int r : Val rT)) xs⌝ ∗ ↯ (F xs))) := by
  iintro Hcredit
  iapply ((RecycledSamples.recycledSamples_zero_distSpec (rT := rT) (GF := GF) E (-4)).spec F
    (measurable_of_countable _))
  isimp only [MeasureTheory.lintegral_dirac]
  iexact Hcredit

/-- A five-draw batch with infinite credit on any out-of-range output. -/
example (E : CoPset) (R : IProp GF) :
    ⊢ R -∗ ↯ (∫⁻ xs, (if ∀ x ∈ xs, x < 6 then 0 else ∞) ∂RecycledSamples.law 6 5) -∗
      tglWp E pl(&Occil.Weighted.recycledSamples #int (6 : ℤ) #int (5 : ℤ))
        (fun v => iprop(R ∗ ∃ xs : List ℕ,
          ⌜v = listVal (fun r : ℕ => (Val.int r : Val rT)) xs⌝ ∗
            ↯ (if ∀ x ∈ xs, x < 6 then 0 else ∞))) := by
  iintro HR Hcredit
  iapply ((RecycledSamples.recycledSamples_distSpec (GF := GF) E 6 5).wp
    _ (measurable_of_countable _) _) $$ Hcredit
  iintro %xs Hcredit
  iframe HR
  iexists xs
  iframe Hcredit
  itrivial

/-- Polya at an integer shape (`2/1`) with success one: ceiling equals the shape. -/
example (E : CoPset) (R : IProp GF) (F : ℕ → ℝ≥0∞) :
    ⊢ R -∗ ↯ (∫⁻ n, F n ∂PolyaRational.law 2 1 3 3 two_pos one_pos three_pos le_rfl) -∗
      tglWp E pl(&Occil.DiscreteExtra.polyaRational #int (2 : ℤ) #int (1 : ℤ)
          #int (3 : ℤ) #int (3 : ℤ))
        (fun v => iprop(R ∗ ∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro HR Hcredit
  iapply ((PolyaRational.polyaRational_distSpec (rT := rT) (GF := GF) E 2 1 3 3
    two_pos one_pos three_pos le_rfl).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iframe HR
  iexists n
  iframe Hcredit
  itrivial

/-- A small fractional shape (`1/7`) and success `1/9`, with unbounded credits. -/
example (E : CoPset) (R : IProp GF) (F : ℕ → ℝ≥0∞) :
    ⊢ R -∗ ↯ (∫⁻ n, F n ∂PolyaRational.law 1 7 1 9 one_pos (by norm_num) one_pos
        (by norm_num)) -∗
      tglWp E pl(&Occil.DiscreteExtra.polyaRational #int (1 : ℤ) #int (7 : ℤ)
          #int (1 : ℤ) #int (9 : ℤ))
        (fun v => iprop(R ∗ ∃ n : ℕ, ⌜v = Val.int (n : ℤ)⌝ ∗ ↯ (F n))) := by
  iintro HR Hcredit
  iapply ((PolyaRational.polyaRational_distSpec (rT := rT) (GF := GF) E 1 7 1 9
    one_pos _ one_pos _).wp F (measurable_of_countable _) _) $$ Hcredit
  iintro %n Hcredit
  iframe HR
  iexists n
  iframe Hcredit
  itrivial

end
