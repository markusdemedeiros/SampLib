import SampLib.LatentDigitStep
import SampLib.LatentDigitPrefix
import SampLib.LatentDigitSource

/-! # Reading a conditional digit cache

The processed prefix determines callback arguments. The unread suffix owns the
remaining linked cells; together they determine the posterior of one latent draw.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentDigits

open scoped Syntax

noncomputable section

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS
open MeasureTheory (Measure IsProbabilityMeasure)

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
variable {Ω : Type} [MeasurableSpace Ω]
local bi (IProp GF)

/-- A read preserves its root and conditions only on the extended cache. -/
def readPost (μ : Measure Ω) (digits : Ω → ℕ → Bool) (root : Loc)
    (processed cached : List Bool) (n : ℕ) (F : Ω → ℝ≥0∞) (result : Val rT) : IProp GF :=
  iprop(∃ q : List Bool,
    ⌜UniformBag.readRefines cached n q ∧
      μ (DigitPosterior.cylinder digits (processed ++ q)) ≠ 0 ∧
      result = LatentReal.intervalVal (readInterval processed q n)⌝ ∗
    UniformBag.owns root q ∗ ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits (processed ++ q)))

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
/-- Reattaching the retained head preserves the updated whole-world posterior. -/
theorem readPost_advance (μ : Measure Ω) (digits : Ω → ℕ → Bool)
    (root tail : Loc) (processed cached unread : List Bool) (b : Bool) (n : ℕ)
    (hs : UniformBag.stepRefines cached b unread) (F : Ω → ℝ≥0∞) (v : Val rT) :
    iprop(appHeapFrag root (UniformBag.nodeVal b tail) ∗
      readPost μ digits tail (processed ++ [b]) unread n F v) ⊢
      readPost μ digits root processed cached (n + 1) F v := by
  iintro ⟨Hroot, Hpost⟩
  isimp only [readPost] at Hpost
  icases Hpost with ⟨%q, %hq, Htail, Hcredit⟩
  rcases hq with ⟨hread, hp, hv⟩
  have hn : n ≤ q.length := by rw [hread.2]; exact le_max_right _ _
  have hI := readInterval_advance processed q b n hn
  isimp only [List.append_assoc, List.singleton_append] at Hcredit
  isimp only [readPost]
  iexists b :: q
  isplit
  · ipureintro
    refine ⟨readRefines_step hs hread, ?_, ?_⟩
    · simpa only [List.append_assoc, List.singleton_append] using hp
    · exact hv.trans (congrArg LatentReal.intervalVal hI)
  isplitl [Hroot Htail]
  · isimp only [UniformBag.owns]
    iexists tail
    iframe Hroot Htail
  iexact Hcredit

omit [ProbLangDist.IsUniformInt rT] in
/-- Requesting no further digits neither samples nor changes the existing posterior. -/
theorem twp_read_zero (E : CoPset) (μ : Measure Ω) (digits : Ω → ℕ → Bool)
    (nextBit : Val rT) (root : Loc) (processed cached : List Bool)
    (hp : μ (DigitPosterior.cylinder digits (processed ++ cached)) ≠ 0)
    (F : Ω → ℝ≥0∞) :
    iprop(UniformBag.owns root cached ∗
      ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits (processed ++ cached))) ⊢
      tglWp E pl(&(Syntax.readVal nextBit).fst #loc root #int (0 : ℤ)
        #int (UniformBag.rank processed) #int (2 ^ processed.length))
        (readPost μ digits root processed cached 0 F) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply Syntax.twp_read_apply
  unfold Syntax.openedReadCode
  twp_pures
  twp_value
  imodintro
  isimp only [readPost]
  iexists cached
  iframe Hstate Hcredit
  ipureintro
  refine ⟨⟨List.prefix_refl _, by simp⟩, hp, ?_⟩
  apply Val.ext
  simp [LatentReal.intervalVal, readInterval, UniformBag.rank]
  rfl

/-- Finite reads reveal exactly the requested digits and preserve every previously cached bit. -/
theorem twp_read (E : CoPset) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (digits : Ω → ℕ → Bool) (hd : ∀ n, Measurable (fun x => digits x n))
    (nextBit : Val rT) (hnext : IsNextDigitSpec (GF := GF) E μ digits hd nextBit)
    (root : Loc) (processed cached : List Bool) (n : ℕ)
    (hp : μ (DigitPosterior.cylinder digits (processed ++ cached)) ≠ 0)
    (F : Ω → ℝ≥0∞) :
    iprop(UniformBag.owns root cached ∗
      ↯ (∫⁻ x, F x ∂DigitPosterior.law μ digits (processed ++ cached))) ⊢
      tglWp E pl(&(Syntax.readVal nextBit).fst #loc root #int (n : ℤ)
        #int (UniformBag.rank processed) #int (2 ^ processed.length))
        (readPost μ digits root processed cached n F) := by
  induction n generalizing root processed cached with
  | zero => exact twp_read_zero E μ digits nextBit root processed cached hp F
  | succ n ih =>
    cases cached with
    | nil =>
      iintro ⟨Hroot, Hcredit⟩
      iapply Syntax.twp_read_apply
      unfold Syntax.openedReadCode
      twp_pure
      twp_pure
      isimp only [UniformBag.owns] at Hroot
      twp_bind pl(!#loc root)
      iapply twp_load
      iframe Hroot
      iintro Hroot
      iterate 3 twp_pure
      isimp only [Syntax.bind, Exp.openRec, Syntax.open_value, ClosedExp.openRec]
      twp_bind (Syntax.fresh nextBit root (UniformBag.rank processed)
        (2 ^ processed.length))
      iapply tglWp_wand
      isplitl [Hroot Hcredit]
      · iapply twp_fresh E μ digits hd nextBit hnext root
          (⟨processed, by simpa only [List.append_nil] using hp⟩ : State μ digits) F
        isimp only [List.append_nil] at Hcredit
        isimp only [UniformBag.owns]
        iframe Hroot Hcredit
      iintro %v ⟨%b, %tail, %hv, Hroot, Htail, Hcredit⟩
      rcases hv with ⟨rfl, hchild⟩
      let nextPrefix := processed ++ [b]
      have hnum := rank_extend processed b
      have hden : (2 : ℤ) ^ (processed ++ [b]).length = 2 ^ processed.length * 2 := by
        simp [pow_succ]
      cases b <;> iterate 9 twp_pure
      all_goals
        rw [Nat.cast_add_one, add_sub_cancel_right]
        simp only [Bool.false_eq_true, ite_false, ite_true] at hnum
        rw [← hnum, ← hden]
        let recurse : Exp rT := pl%
          &(Syntax.readVal nextBit).fst #loc tail #int (n : ℤ)
            #int (UniformBag.rank nextPrefix) #int (2 ^ nextPrefix.length)
        ieval (change _ ⊢ tglWp E recurse _)
        iapply tglWp_wand
        isplitl [Htail Hcredit]
        · iapply ih tail nextPrefix [] (by simpa only [nextPrefix, List.append_nil] using hchild)
          isimp only [List.append_nil]
          iframe Htail Hcredit
        iintro %v Hpost
        iapply readPost_advance μ digits root tail processed [] [] _ n (Or.inl ⟨rfl, rfl⟩) F v
        iframe Hroot Hpost
    | cons b cached =>
      iintro ⟨Hroot, Hcredit⟩
      isimp only [UniformBag.owns] at Hroot
      icases Hroot with ⟨%tail, Hroot, Htail⟩
      iapply Syntax.twp_read_apply
      unfold Syntax.openedReadCode
      twp_pure
      twp_pure
      twp_bind pl(!#loc root)
      iapply twp_load
      iframe Hroot
      iintro Hroot
      iterate 3 twp_pure
      isimp only [Syntax.bind, Exp.openRec, Syntax.open_value, ClosedExp.openRec]
      let nextPrefix := processed ++ [b]
      have hnum := rank_extend processed b
      have hden : (2 : ℤ) ^ (processed ++ [b]).length = 2 ^ processed.length * 2 := by
        simp [pow_succ]
      cases b <;> iterate 9 twp_pure
      all_goals
        rw [Nat.cast_add_one, add_sub_cancel_right]
        simp only [Bool.false_eq_true, ite_false, ite_true] at hnum
        rw [← hnum, ← hden]
        let recurse : Exp rT := pl%
          &(Syntax.readVal nextBit).fst #loc tail #int (n : ℤ)
            #int (UniformBag.rank nextPrefix) #int (2 ^ nextPrefix.length)
        ieval (change _ ⊢ tglWp E recurse _)
        iapply tglWp_wand
        isplitl [Htail Hcredit]
        · iapply ih tail nextPrefix cached
            (by simpa only [nextPrefix, List.append_assoc, List.singleton_append] using hp)
          isimp only [nextPrefix, List.append_assoc, List.singleton_append]
          iframe Htail Hcredit
        iintro %v Hpost
        iapply readPost_advance μ digits root tail processed (_ :: cached) cached _ n
          (Or.inr rfl) F v
        iframe Hroot Hpost

end specification

end

end SampLib.LatentDigits
