import SampLib.LatentRepresentedMultiplication
import SampLib.LatentRepresentedAddition
import SampLib.LatentWorldRelations
import SampLib.LatentMeasuredError
import SampLib.Syntax.RepresentedIntegerPower

/-! # Represented integer powers over one shared latent world

The binary multiplication tree is exactly the source's repeated-squaring plan.
Its intervals use the actual four-corner products, including aliased squares.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.LatentReal.IntegerPower

noncomputable section

private inductive Tree where
  | one
  | source
  | product (left right : Tree)

private def tree (n : ℕ) : Tree :=
  if n = 0 then .one else if n = 1 then .source else
    let half := tree (n / 2)
    let square := Tree.product half half
    if n % 2 = 0 then square else .product .source square
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

private def degree : Tree → ℕ
  | .one => 0
  | .source => 1
  | .product a b => degree a + degree b

private theorem tree_zero : tree 0 = .one := by rw [tree]; simp

private theorem tree_one : tree 1 = .source := by rw [tree]; simp

private theorem tree_step (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    tree n = if n % 2 = 0 then .product (tree (n / 2)) (tree (n / 2))
      else .product .source (.product (tree (n / 2)) (tree (n / 2))) := by
  rw [tree]
  simp only [h0, h1, ite_false]

private theorem tree_degree (n : ℕ) : degree (tree n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h0 : n = 0
    · subst n
      rw [tree_zero]
      rfl
    by_cases h1 : n = 1
    · subst n
      rw [tree_one]
      rfl
    have hh : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
    rw [tree_step n h0 h1]
    split_ifs with he
    · simp only [degree, ih _ hh]
      omega
    · simp only [degree, ih _ hh]
      omega

variable {Ω S : Type} [MeasurableSpace Ω]

private def world (D : Model Ω S) : Tree → {M : Model Ω S // D.SameWorld M}
  | .one => ⟨D.constant 1, D.sameWorld_constant 1⟩
  | .source => ⟨D, .refl D⟩
  | .product a b =>
    let L := world D a
    let R := world D b
    let hworld := Model.SameWorld.between L.property R.property
    ⟨L.val.multiply R.val hworld, L.property.trans hworld.multiply_left⟩

private def represented (D : Model Ω S) (R : Representation D) :
    (t : Tree) → Representation (world D t).val
  | .one => Representation.point D 1 1 1 (by norm_num) (by norm_num)
  | .source => R
  | .product a b => Representation.multiply (world D a).val (world D b).val
      (Model.SameWorld.between (world D a).property (world D b).property)
      (represented D R a) (represented D R b)

private def handle {rT : Type} (source : Val rT) : Tree → Val rT
  | .one => LatentRational.value 1 1
  | .source => source
  | .product a b => multiplyVal (handle source a) (handle source b)

/-- The model retains the original posterior and follows the source multiplication tree. -/
def model (D : Model Ω S) (n : ℕ) : Model Ω S := (world D (tree n)).val

def representation (D : Model Ω S) (R : Representation D) (n : ℕ) : Representation (model D n) :=
  represented D R (tree n)

def value {rT : Type} (source : Val rT) (n : ℕ) : Val rT := handle source (tree n)

@[simp] theorem value_zero {rT : Type} (source : Val rT) :
    value source 0 = LatentRational.value 1 1 := by rw [value, tree_zero]; rfl

@[simp] theorem value_one {rT : Type} (source : Val rT) : value source 1 = source := by
  rw [value, tree_one]
  rfl

private theorem value_step {rT : Type} (source : Val rT) (n : ℕ) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    value source n = if n % 2 = 0 then multiplyVal (value source (n / 2)) (value source (n / 2))
      else multiplyVal source (multiplyVal (value source (n / 2)) (value source (n / 2))) := by
  rw [value, tree_step n h0 h1]
  split_ifs <;> rfl

theorem sameWorld (D : Model Ω S) (n : ℕ) : D.SameWorld (model D n) :=
  (world D (tree n)).property

private theorem world_value (D : Model Ω S) (t : Tree) (x : Ω) :
    (world D t).val.value x = D.value x ^ degree t := by
  induction t with
  | one => simp [world, Model.constant, degree]
  | source => simp [world, degree]
  | product a b ha hb =>
    change (world D a).val.value x * (world D b).val.value x = _
    rw [ha, hb]
    exact (pow_add _ _ _).symm

/-- Repeated squaring represents the ordinary power, including zero and negative bases. -/
theorem value_eq (D : Model Ω S) (n : ℕ) (x : Ω) : (model D n).value x = D.value x ^ n := by
  rw [model, world_value, tree_degree]

private theorem product_measurableError (L R : Model Ω S) (hworld : L.SameWorld R)
    (hL : L.MeasurableError) (hR : R.MeasurableError) :
    (L.multiply R hworld).MeasurableError := by
  intro n
  exact measurable_const.mul ((((hL n).mul R.measurable_value.abs).add
    (L.measurable_value.abs.mul (hR n))).add ((hL n).mul (hR n)))

/-- Measurable source errors remain measurable through every actual multiplication. -/
theorem measurableError (D : Model Ω S) (hD : D.MeasurableError) (n : ℕ) :
    (model D n).MeasurableError := by
  have hall (t : Tree) : (world D t).val.MeasurableError := by
    induction t with
    | one => exact fun _ => measurable_const
    | source => exact hD
    | product a b ha hb =>
      exact product_measurableError _ _
        (Model.SameWorld.between (world D a).property (world D b).property) ha hb
  exact hall (tree n)

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

private theorem tree_oracleSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (source : Val rT) (hsource : IsRepresentedViewSpec E D R P source)
    (t : Tree) :
    IsRepresentedViewSpec E (world D t).val (represented D R t) P (handle source t) := by
  induction t with
  | one => exact represented_point_viewSpec E D P 1 1 1 (by norm_num) (by norm_num)
  | source => exact hsource
  | product a b ha hb => exact represented_multiply_oracleSpec E _ _ _ _ _ P _ _ ha hb

/-- Aliased factors are observed sequentially using the same whole-world ownership. -/
theorem oracleSpec (E : CoPset) (D : Model Ω S) (R : Representation D)
    (P : S → IProp GF) (source : Val rT) (hsource : IsRepresentedViewSpec E D R P source)
    (n : ℕ) :
    IsRepresentedViewSpec E (model D n) (representation D R n) P (value source n) :=
  tree_oracleSpec E D R P source hsource (tree n)

private theorem zero_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 0) = decide (n = 0) := by
  change decide ((n : ℤ) = 0) = decide (n = 0)
  simp

private theorem one_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int (n : ℤ) : BaseLit rT) == .int 1) = decide (n = 1) := by
  change decide ((n : ℤ) = 1) = decide (n = 1)
  simp

private theorem parity_test {rT : Type} [BEq rT] (n : ℕ) :
    ((BaseLit.int ((n : ℤ) % 2) : BaseLit rT) == .int 0) = decide (n % 2 = 0) := by
  change decide ((n : ℤ) % 2 = 0) = decide (n % 2 = 0)
  exact decide_eq_decide.mpr (by omega)

open scoped SampLib.LatentReal.IntegerPower.Program

attribute [local pl_step_simp] ClosedExp.openRec ClosedExp.closeRec ProbLang.openRec_val_fst

/-- Capturing a power does not read the source or consume its joint continuation credit. -/
theorem twp_integerPowerReal (E : CoPset) (source : Val rT) (P : S → IProp GF) (s : S) (n : ℕ) :
    iprop(P s) ⊢ tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
      (fun v => ViewOwns (value source n) P v s) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    iintro Hstate
    iapply Program.twp_open E source (n : ℤ)
    unfold Program.body
    twp_pure
    twp_pure
    twp_pure
    rw [zero_test]
    by_cases h0 : n = 0
    · subst n
      rw [decide_eq_true rfl]
      twp_pures
      twp_value
      imodintro
      isimp only [ViewOwns, value_zero]
      iframe Hstate
      ipureintro
      apply Val.ext
      rfl
    · rw [decide_eq_false h0]
      twp_pure
      twp_pure
      rw [one_test]
      by_cases h1 : n = 1
      · subst n
        rw [decide_eq_true rfl]
        twp_pure
        ieval (change _ ⊢ tglWp E (Exp.ofVal source) _)
        iapply tglWp_value
        isimp only [ViewOwns, value_one]
        iframe Hstate
      · rw [decide_eq_false h1]
        twp_pure
        twp_pure
        twp_bind pl(&Occil.PSRN.integerPowerReal &source.fst #int ((n / 2 : ℕ) : ℤ))
        iapply tglWp_wand
        isplitl [Hstate]
        · iapply ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)) $$ Hstate
        iintro %half Hstate
        isimp only [ViewOwns] at Hstate
        icases Hstate with ⟨%hhalf, Hstate⟩
        subst half
        twp_pure
        twp_bind pl(&Occil.PSRN.multiply &(value source (n / 2)).fst
          &(value source (n / 2)).fst)
        iapply tglWp_wand
        isplitl [Hstate]
        · iapply twp_multiply E (value source (n / 2)) (value source (n / 2)) P s $$ Hstate
        iintro %square Hstate
        isimp only [ViewOwns] at Hstate
        icases Hstate with ⟨%hsquare, Hstate⟩
        subst square
        twp_pure
        twp_pure
        twp_pure
        rw [parity_test]
        by_cases he : n % 2 = 0
        · rw [decide_eq_true he]
          twp_pure
          ieval (change _ ⊢ tglWp E (Exp.ofVal
            (multiplyVal (value source (n / 2)) (value source (n / 2)))) _)
          iapply tglWp_value
          isimp only [ViewOwns, value_step source n h0 h1, ite_eq_left he]
          iframe Hstate
        · rw [decide_eq_false he]
          twp_pure
          isimp only [value_step source n h0 h1, ite_eq_right he]
          iapply twp_multiply E source (multiplyVal (value source (n / 2))
            (value source (n / 2))) P s $$ Hstate

/-- Construction leaves arbitrary joint credit unspent under the unchanged posterior. -/
theorem twp_integerPowerReal_credit (E : CoPset) (D : Model Ω S) (source : Val rT)
    (P : S → IProp GF) (s : S) (n : ℕ) (G : Ω → ℝ≥0∞) :
    iprop(P s ∗ ↯ (∫⁻ x, G x ∂D.posterior s)) ⊢
      tglWp E pl(&Occil.PSRN.integerPowerReal &source.fst #int (n : ℤ))
        (fun v => iprop(ViewOwns (value source n) P v s ∗
          ↯ (∫⁻ x, G x ∂(model D n).posterior s))) := by
  iintro ⟨Hstate, Hcredit⟩
  iapply tglWp_wand
  isplitl [Hstate]
  · iapply twp_integerPowerReal E source P s n $$ Hstate
  iintro %v Hstate
  isimp only [(sameWorld D n).posterior_eq s]
  iframe Hstate Hcredit

end specification

end

end SampLib.LatentReal.IntegerPower
