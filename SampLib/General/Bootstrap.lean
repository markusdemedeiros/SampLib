import SampLib.Core.GeneralSyntax
import SampLib.Combinatorial.SampleWithReplacement
import Samplers.General.DataModels

/-! # Independent empirical bootstrap data sets -/

open ProbLang
open scoped ENNReal

namespace SampLib.Bootstrap

noncomputable section

section mathematics

open MeasureTheory

/-- Each bootstrap data set has `n` independent empirical positions. -/
abbrev blockLaw (n : ℕ) [NeZero n] :=
  SampleWithReplacement.law (Choice.law n) n

/-- The bootstrap replicates are independent, each with the original sample size. -/
def law (n : ℕ) [NeZero n] (replicates : ℕ) :=
  SampleWithReplacement.law (blockLaw n) replicates

instance (n : ℕ) [NeZero n] (replicates : ℕ) :
    IsProbabilityMeasure (law n replicates) := by
  dsimp [law]
  infer_instance

end mathematics

private def blockSampler {rT : Type _} [ProbLangℝ rT] {α : Type _}
    (encode : α → Val rT) (xs : List α) : Val rT :=
  ⟨.lam (.app (.app Occil.sampleWithReplacement (listVal encode xs).fst)
    (.lit (.int (xs.length : ℤ)))), .lam (by is_lc), by is_lc⟩

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type _} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF] {α : Type _}
local bi (IProp GF)

private theorem blockSampler_spec (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] :
    IsDistSpec (GF := GF) E pl(&(blockSampler encode xs).fst #())
      (blockLaw xs.length)
      (fun ys => listVal (fun i => encode (xs.get i)) (List.ofFn ys)) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&Occil.sampleWithReplacement &(listVal encode xs).fst #int (xs.length : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (SampleWithReplacement.sampleWithReplacement_distSpec E encode xs xs.length).spec
      F hF $$ Hcredit

/-- Two applications of independent repetition give the nested bootstrap law. -/
theorem twp_bootstrap (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] (replicates : ℕ)
    (F : (Fin replicates → Fin xs.length → Fin xs.length) → ℝ≥0∞)
    (hF : Measurable F) :
    ⊢ ↯ (∫⁻ ys, F ys ∂law xs.length replicates) -∗
      tglWp E pl(&Occil.General.bootstrap &(listVal encode xs).fst
        #int (replicates : ℤ) #())
        (fun v : Val rT => iprop(∃ ys : Fin replicates → Fin xs.length → Fin xs.length,
          ⌜v = listVal (fun zs => listVal (fun i => encode (xs.get i))
            (List.ofFn zs)) (List.ofFn ys)⌝ ∗ ↯ (F ys))) := by
  iintro Hcredit
  iterate 5 twp_pure
  twp_bind pl(&Occil.length &(listVal encode xs).fst)
  iapply tglWp_wand
  isplitl []
  · iapply twp_length E encode xs
  iintro %v %hv
  subst v
  twp_pure
  simp only [GeneralSyntax.repeatSample_openRec, GeneralSyntax.repeatSample_closeRec,
    SamplerTerms.sampleWithReplacement_openRec, SamplerTerms.sampleWithReplacement_closeRec]
  twp_bind pl(&Occil.repeatSample &(blockSampler encode xs).fst #int (replicates : ℤ))
  iapply (tglWp_mono fun _ => tglWp_value)
  isimp only [law] at Hcredit
  iapply (SampleWithReplacement.repeatSample_distSpec E (blockLaw xs.length)
    (fun zs => listVal (fun i => encode (xs.get i)) (List.ofFn zs))
    (blockSampler encode xs) (blockSampler_spec E encode xs) replicates).spec F hF $$ Hcredit

/-- Typed bootstrap specification on every nonempty empirical data set. -/
theorem bootstrap_distSpec (E : CoPset) (encode : α → Val rT) (xs : List α)
    [NeZero xs.length] (replicates : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.General.bootstrap &(listVal encode xs).fst
      #int (replicates : ℤ) #()) (law xs.length replicates)
      (fun ys => listVal (fun zs => listVal (fun i => encode (xs.get i))
        (List.ofFn zs)) (List.ofFn ys)) where
  spec F hF := wand_entails (twp_bootstrap E encode xs replicates F hF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem emptyBlock_spec (E : CoPset) (encode : α → Val rT) :
    IsDistSpec (GF := GF) E pl(&(blockSampler encode []).fst #())
      (MeasureTheory.Measure.dirac ()) (fun _ : Unit => listVal encode []) where
  spec F hF := by
    iintro Hcredit
    twp_pure
    twp_bind pl(&Occil.sampleWithReplacement &(listVal encode []).fst #int (0 : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (SampleWithReplacement.sampleWithReplacement_zero_distSpec E encode []).spec
      F hF $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
/-- An empty empirical data set produces the requested number of empty replicates. -/
theorem bootstrap_empty_distSpec (E : CoPset) (encode : α → Val rT) (replicates : ℕ) :
    IsDistSpec (GF := GF) E pl(&Occil.General.bootstrap &(listVal encode []).fst
      #int (replicates : ℤ) #())
      (SampleWithReplacement.law (MeasureTheory.Measure.dirac ()) replicates)
      (fun ys => listVal (fun _ : Unit => listVal encode []) (List.ofFn ys)) where
  spec F hF := by
    iintro Hcredit
    iterate 5 twp_pure
    twp_bind pl(&Occil.length &(listVal encode []).fst)
    iapply tglWp_wand
    isplitl []
    · iapply twp_length E encode []
    iintro %v %hv
    subst v
    twp_pure
    simp only [GeneralSyntax.repeatSample_openRec, GeneralSyntax.repeatSample_closeRec,
      SamplerTerms.sampleWithReplacement_openRec, SamplerTerms.sampleWithReplacement_closeRec]
    twp_bind pl(&Occil.repeatSample &(blockSampler encode []).fst #int (replicates : ℤ))
    iapply (tglWp_mono fun _ => tglWp_value)
    iapply (SampleWithReplacement.repeatSample_distSpec E (MeasureTheory.Measure.dirac ())
      (fun _ : Unit => listVal encode []) (blockSampler encode [])
      (emptyBlock_spec E encode) replicates).spec F hF $$ Hcredit

end specification

end

end SampLib.Bootstrap
