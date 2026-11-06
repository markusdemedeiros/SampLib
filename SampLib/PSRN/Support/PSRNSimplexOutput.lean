import SampLib.PSRN.Support.PSRNSimplexSource
import SampLib.PSRN.Support.LatentRational
import SampLib.Latent.LatentVectorSpec
import SampLib.PSRN.PSRNSimplexMany
import SampLib.PSRN.Laws.UniformSimplexLaw

/-! # A uniform output protocol for every positive simplex dimension

A singleton returns the constant unit oracle and leaves the exponential world
unobserved. Larger vectors normalize the actual independent exponentials.
-/

open ProbLang

namespace SampLib.PSRNSimplex

noncomputable section

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {GF : BundledGFunctors} [ErisWpGS (rT := rT) GF]
local bi (IProp GF)

def singletonHandles : Fin 1 → Val rT := fun _ => LatentRational.value 1 1

/-- The constant branch leaves every caller resource untouched. -/
theorem twp_singleton (E : CoPset) (P : IProp GF) :
    P ⊢ tglWp E pl(&Occil.PSRN.newSimplex #1 #())
      (fun v => iprop(⌜v = LatentReal.vectorVal singletonHandles⌝ ∗ P)) := by
  iintro HP
  iapply Program.twp_open E 1 _
  unfold Program.openedBody
  twp_pures
  twp_value
  imodintro
  iframe HP
  ipureintro
  apply Val.ext
  simp [LatentReal.vectorVal, singletonHandles, List.ofFn_succ, List.ofFn_zero,
    listVal, LatentRational.value]
  rfl

end

end SampLib.PSRNSimplex

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNSimplex

noncomputable section

open LatentReal

def output (n : ℕ) (i : Fin n) : Model (World n) (State n) :=
  if n = 1 then (world n).constant 1 else normalized n i

theorem output_one {n : ℕ} (hn : n = 1) : output n = fun _ => (world n).constant 1 := by
  funext i
  simp [output, hn]

theorem output_many {n : ℕ} (hn : n ≠ 1) : output n = normalized n := by
  funext i
  simp [output, hn]

theorem output_sameWorld (n : ℕ) (i : Fin n) : (world n).SameWorld (output n i) := by
  unfold output
  split
  · exact (world n).sameWorld_constant 1
  · exact Normalization.sameWorld _ _ _ _ i

section mathematics

open MeasureTheory

/-- Both branches identify the uniform law on the open simplex. -/
theorem output_law (n : ℕ) :
    vectorLaw (world n) (output n) (initial n) = PSRNDirichletLaw.simplex n := by
  by_cases hn : n = 1
  · subst n
    rw [output_one rfl, PSRNDirichletLaw.simplex, PSRNDirichletLaw.law_singleton]
    change ((world 1).posterior (initial 1)).map (fun _ => fun _ : Fin 1 => (1 : ℝ)) = _
    simp
  · rw [output_many hn]
    exact normalized_law n

/-- The canonical identification: `m!` times Lebesgue measure on the open simplex
`{y > 0, ∑ y < 1}`, completed by the last coordinate `1 - ∑ y`. -/
theorem output_law_uniform (m : ℕ) :
    vectorLaw (world (m + 1)) (output (m + 1)) (initial (m + 1)) =
      (UniformSimplex.law m).map UniformSimplex.embed :=
  (output_law (m + 1)).trans (UniformSimplex.simplex_eq m)

/-- The first `m` output coordinates have density `m!` on the open simplex region. -/
theorem output_firstCoordinates (m : ℕ) :
    (vectorLaw (world (m + 1)) (output (m + 1)) (initial (m + 1))).map
      (fun x i => x (Fin.castSucc i)) = UniformSimplex.law m := by
  rw [output_law]
  exact UniformSimplex.simplex_firstCoordinates m

end mathematics

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A singleton owns only its constant handles; larger vectors retain the original family. -/
def outputOwns (n : ℕ) (handles : Fin n → Val rT) (s : State n) : IProp GF :=
  if n = 1 then iprop(⌜∀ i, handles i = LatentRational.value 1 1⌝) else normalizedOwns n handles s

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem outputOwns_one {n : ℕ} (hn : n = 1) (handles : Fin n → Val rT) (s : State n) :
    outputOwns (GF := GF) n handles s = iprop(⌜∀ i, handles i = LatentRational.value 1 1⌝) := by
  simp [outputOwns, hn]

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem outputOwns_many {n : ℕ} (hn : n ≠ 1) :
    outputOwns (GF := GF) n = normalizedOwns (rT := rT) n := by
  funext handles s
  simp [outputOwns, hn]

omit [ProbLangDist.IsUniformInt rT] in
/-- The singleton handles all read the point interval of `1`, under any refined state. -/
theorem singleton_coordinateSpec (E : CoPset) (n : ℕ) (hn : n = 1)
    (handles : Fin n → Val rT) (i : Fin n) :
    IsViewSpec (GF := GF) E (output n i) (outputOwns n handles) (handles i) := by
  have hpoint : IsViewSpec (GF := GF) E (output n i) (outputOwns n handles)
      (LatentRational.value 1 1) := by
    rw [output_one hn]
    exact (represented_point_viewSpec (rT := rT) (GF := GF) E (world n)
      (outputOwns n handles) 1 1 1 (by decide) (by norm_num)).forget
  refine ⟨fun v s k F hF => ?_⟩
  iintro ⟨Hstate, Hcredit⟩
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hv, Hstate⟩
  rw [outputOwns_one hn]
  icases Hstate with %hh
  subst v
  rw [hh i]
  iapply hpoint.observe _ s k F hF
  isplitl []
  · isimp only [ViewOwns]
    rw [outputOwns_one hn]
    ipureintro
    exact ⟨trivial, hh⟩
  iexact Hcredit

theorem output_coordinateSpec (E : CoPset) (n : ℕ) (handles : Fin n → Val rT) (i : Fin n) :
    IsViewSpec (GF := GF) E (output n i) (outputOwns n handles) (handles i) := by
  by_cases hn : n = 1
  · exact singleton_coordinateSpec E n hn handles i
  have hmany : 2 ≤ n := by have := i.pos; omega
  rw [output_many hn, outputOwns_many hn]
  exact ((many_vectorSpec E n hmany).coordinate handles i).forget

end specification

end

end SampLib.PSRNSimplex
