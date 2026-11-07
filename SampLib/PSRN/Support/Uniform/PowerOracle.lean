import SampLib.PSRN.Support.Uniform.PowerModel
import SampLib.PSRN.Support.Represented.Unary
import Samplers.PSRN.Uniform

/-! # Observing a rational power of one deferred uniform

Each branch of the power owns the one uniform cache through its closures. Every read
observes that shared uniform. The positive branch runs repeated squaring and then a root
unless the degree is one.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.PSRNPowerUniform

noncomputable section

open LatentReal

namespace Program

/-- The root constructor: guard the degree, return the source for degree one. -/
def rootBody {rT : Type} : Exp rT :=
  .cond (.binop .le (.bvar 0) (.lit (.int 0))) .fail
    (.cond (.binop .eq (.bvar 0) (.lit (.int 1))) (.bvar 1) (.lam Root.Program.observerBody))

theorem root_eq {rT : Type} : (Occil.PSRN.root : Exp rT) = CurriedStep.lambdas 2 rootBody := by
  kernel_rfl

theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

theorem rootBody_lcb {rT : Type} : Exp.lcb 2 (rootBody : Exp rT) = true := by kernel_rfl

end Program

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

/-- A power closure owns exactly the one uniform cache it multiplies. -/
def powerOwns (a : ℕ) (v : Val rT) (p : List Bool) : IProp GF :=
  iprop(∃ source : Val rT,
    ViewOwns (IntegerPower.value source a) (LatentUniform.owns source) v p)

def rootedOwns (a b : ℕ) : Val rT → List Bool → IProp GF :=
  if b = 1 then powerOwns a else Root.owns (power a).1 b (powerOwns a)

/-- The constant branch owns nothing; the others retain the uniform through each closure. -/
def owns (a : ℤ) (b : ℕ) : Val rT → List Bool → IProp GF :=
  if a = 0 then ViewOwns (LatentRational.value 1 1) (fun _ => iprop(emp))
  else if 0 < a then rootedOwns a.natAbs b
  else RepresentedReciprocal.owns (rooted a.natAbs b).1 (rootedOwns a.natAbs b)

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem owns_zero (b : ℕ) :
    owns (GF := GF) 0 b = ViewOwns (LatentRational.value (rT := rT) 1 1) (fun _ => iprop(emp)) := by
  simp [owns]

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem owns_pos {a : ℤ} (b : ℕ) (ha : 0 < a) :
    owns (rT := rT) (GF := GF) a b = rootedOwns a.natAbs b := by
  simp [owns, ha.ne', ha]

omit [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT] in
theorem owns_neg {a : ℤ} (b : ℕ) (ha : a < 0) :
    owns (rT := rT) (GF := GF) a b =
      RepresentedReciprocal.owns (rooted a.natAbs b).1 (rootedOwns a.natAbs b) := by
  simp [owns, ha.ne, not_lt.mpr ha.le]

theorem powerOracleSpec (E : CoPset) (a : ℕ) :
    IsRepresentedOracleSpec (GF := GF) E (power a).1 (power a).2 (powerOwns a) := by
  refine ⟨fun v p n F hF => ?_⟩
  simp only [power]
  iintro ⟨Hstate, Hcredit⟩
  isimp only [powerOwns] at Hstate
  icases Hstate with ⟨%source, Hstate⟩
  have hpower := IntegerPower.oracleSpec E U LatentUniform.representation
    (LatentUniform.owns source) source
    ((LatentUniform.representedOracleSpec (rT := rT) (GF := GF) E).viewSpec source) a
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hv, Hstate⟩
  subst v
  iapply hpower.wp p n F hF _ $$ Hstate Hcredit
  iintro %t %I %hI Hstate Hcredit
  iexists t, I
  isplitl []
  · ipureintro
    exact ⟨rfl, hI⟩
  iframe Hcredit
  isimp only [powerOwns]
  iexists source
  isimp only [ViewOwns]
  iframe Hstate

theorem rootedOracleSpec (E : CoPset) (a b : ℕ) (hb : 0 < b) :
    IsRepresentedOracleSpec (GF := GF) E (rooted a b).1 (rooted a b).2 (rootedOwns a b) := by
  by_cases h1 : b = 1
  · subst b
    rw [show rootedOwns (rT := rT) (GF := GF) a 1 = powerOwns a by simp [rootedOwns],
      rooted_one]
    exact powerOracleSpec E a
  · rw [show rootedOwns (rT := rT) (GF := GF) a b = Root.owns (power a).1 b (powerOwns a) by
      simp [rootedOwns, h1], rooted_root a h1]
    exact Root.representedOracleSpec E (power a).1
      (IntegerPower.measurableError U (fun _ => measurable_const) a) (powerOwns a)
      (powerOracleSpec E a).forget b (by omega)

/-- Every read observes the one shared uniform through the selected branch. -/
theorem representedOracleSpec (E : CoPset) (a : ℤ) (b : ℕ) (hb : 0 < b) :
    IsRepresentedOracleSpec (GF := GF) E (model a b) (representation a b) (owns a b) := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [owns_neg b ha]
    unfold model representation
    rw [stage_neg b ha]
    exact RepresentedReciprocal.oracleSpec E _ _ _ (rootedOracleSpec E _ b hb)
  · rw [owns_zero b]
    unfold model representation
    rw [stage_zero b]
    exact represented_point_viewSpec E U _ 1 1 1 (by decide) (by norm_num)
  · rw [owns_pos b ha]
    unfold model representation
    rw [stage_pos b ha]
    exact rootedOracleSpec E _ b hb

omit [ProbLangDist.IsUniformInt rT] in
/-- A degree-one root returns its source handle unchanged. -/
theorem twp_root_one (E : CoPset) (source : Val rT) (P : List Bool → IProp GF) (p : List Bool) :
    P p ⊢ tglWp E pl(&Occil.PSRN.root &source.fst #1)
      (fun v => ViewOwns source P v p) := by
  have h := CurriedStep.twp_apply E [] [source, .int 1] Program.rootBody
    (Program.rootBody_lcb (rT := rT)) (fun v => ViewOwns source P v p)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, ← Program.root_eq,
    CurriedStep.application, CurriedStep.context, List.map_cons, List.map_nil,
    Ectx.fill, List.foldl_cons, List.foldl_nil, Function.flip_def, EctxItem.fillItem,
    Exp.ofVal] at h
  iintro Hstate
  iapply h
  simp only [CurriedStep.opened, Program.rootBody, List.length_cons, List.length_nil,
    Exp.openRec, Val.int, Nat.reduceAdd, ↓reduceIte, Nat.succ_ne_self,
    ← Exp.open_lc 0 _ source.fst source.lc]
  twp_pure
  twp_pure
  twp_pure
  twp_pure
  ieval (change _ ⊢ tglWp E (Exp.ofVal source) _)
  iapply tglWp_value
  isimp only [ViewOwns]
  iframe Hstate

omit [ProbLangDist.IsUniformInt rT] in
/-- The source's positive-power branch: repeated squaring, then a root unless `b = 1`. -/
theorem twp_rooted (E : CoPset) (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (source : Val rT)
    (p : List Bool) :
    LatentUniform.owns source p ⊢
      tglWp E pl(&Occil.PSRN.root (&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        #int (b : ℤ)) (fun v => rootedOwns n b v p) := by
  iintro Hstate
  twp_bind pl(&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply IntegerPower.twp_integerPowerReal E source (LatentUniform.owns source) p n $$ Hstate
  iintro %power Hstate
  isimp only [ViewOwns] at Hstate
  icases Hstate with ⟨%hpower, Hstate⟩
  subst power
  simp only [Exp.ofVal]
  by_cases h1 : b = 1
  · subst b
    rw [show rootedOwns (rT := rT) (GF := GF) n 1 = powerOwns n by simp [rootedOwns],
      Nat.cast_one]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply twp_root_one E (IntegerPower.value source n) (LatentUniform.owns source) p
        $$ Hstate
    iintro %v Hstate
    isimp only [powerOwns]
    iexists source
    iexact Hstate
  · rw [show rootedOwns (rT := rT) (GF := GF) n b = Root.owns (power n).1 b (powerOwns n) by
      simp [rootedOwns, h1]]
    iapply tglWp_wand
    isplitl [Hstate]
    · iapply Root.Program.twp_root E (IntegerPower.value source n) b (by omega)
        (powerOwns n (IntegerPower.value source n)) p
      isimp only [powerOwns]
      iexists source
      isimp only [ViewOwns]
      iframe Hstate
    iintro %v Hstate
    isimp only [ViewOwns] at Hstate
    icases Hstate with ⟨%hv, Hstate⟩
    isimp only [Root.owns]
    iexists IntegerPower.value source n
    iframe Hstate
    ipureintro
    exact ⟨hv, admissible n b hn p⟩

end specification

end

end SampLib.PSRNPowerUniform
