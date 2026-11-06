import SampLib.Bernoulli.Laws.FactorialSeriesKernel
import SampLib.Bernoulli.Laws.FactorialSeriesMean
import SampLib.Latent.UniformBagBracket
import SampLib.Bernoulli.CoinProduct
import Samplers.Lazy

/-! # Lazy factorial-series Bernoulli factories

An independent first-failure count specifies the random threshold. Every
comparison refines the posterior of the same cached uniform point.
-/

open ProbLang
open scoped ENNReal

namespace SampLib.FactorialSeriesFactory

noncomputable section

open FactorialSeries

/-- The exact special-function bias identified by the independent threshold model. -/
def bias (m : Mode) (p : unitInterval) : unitInterval := ⟨value m p, value_mem m p⟩

@[simp] theorem bias_coe (m : Mode) (p : unitInterval) : (bias m p : ℝ) = value m p := rfl

@[simp] theorem bias_exp_coe (p : unitInterval) : (bias .exp p : ℝ) = Real.exp (-(p : ℝ)) := rfl

private theorem meanBias_eq (m : Mode) (p : unitInterval) : meanBias m p = bias m p :=
  Subtype.ext (mean_eq_value m p)

theorem factorialSeriesFactory_lc {rT : Type} :
    (Occil.factorialSeriesFactory : Exp rT).IsLocallyClosed := by is_lc

theorem factorialSeriesFactory_fv {rT : Type} :
    (Occil.factorialSeriesFactory : Exp rT).fv = ∅ := by
  simp [Occil.factorialSeriesFactory, UniformBag.uniformBagLess_fv,
    Occil.newUniformBag, Exp.fv]

@[simp] theorem factorialSeriesFactory_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.factorialSeriesFactory = Occil.factorialSeriesFactory :=
  (Exp.open_lc k e _ factorialSeriesFactory_lc).symm

@[simp] theorem factorialSeriesFactory_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.factorialSeriesFactory : Exp rT) = Occil.factorialSeriesFactory :=
  Exp.closeRec_fresh x _ k (by simp [factorialSeriesFactory_fv])

private theorem newBag_openRec {rT : Type} (k : ℕ) (e : Exp rT) :
    Exp.openRec k e Occil.newUniformBag = Occil.newUniformBag :=
  (Exp.open_lc k e _ (by is_lc)).symm

private theorem newBag_closeRec {rT : Type} (k : ℕ) (x : Var) :
    Exp.closeRec k x (Occil.newUniformBag : Exp rT) = Occil.newUniformBag :=
  Exp.closeRec_fresh x _ k (by simp [Occil.newUniformBag, Exp.fv])

private theorem mode_guard (m : Mode) :
    Bool.or (decide (m.code < 0)) (decide ((2 : ℤ) < m.code)) = false := by
  cases m <;> rfl

private def initialDenominator : Mode → ℕ
  | .exp => 1
  | .cos => 2
  | .sinc => 6

private theorem initial_denominator (m : Mode) : stateDenominator m 0 = initialDenominator m := by
  cases m <;> rfl

private def initialCall {rT : Type} (self : Val rT) (m : Mode) : Exp rT :=
  .app (.lam (.app (.lam (pl% {Exp.bvar 0} #1 {Exp.bvar 1} #0 {Exp.bvar 1} #true))
    self.fst)) (pl% if #int m.code = #0 then #1 else if #int m.code = #1 then #2 else #6)

private def grouped {rT : Type} (coin : Val rT) (m : Mode) : Exp rT :=
  .cond pl(&coin.fst #())
    (.cond pl(#int m.code = #0) pl(#true) pl(&coin.fst #())) pl(#false)

private def firstCredit (p : unitInterval) (m : Mode) (F : Bool → ℝ≥0∞) (b : Bool) : ℝ≥0∞ :=
  if b then if m = .exp then F true else ∫⁻ c, F c ∂RealCoin.law p else F false

private theorem grouped_expectation (p : unitInterval) (m : Mode) (F : Bool → ℝ≥0∞) :
    (∫⁻ b, firstCredit p m F b ∂RealCoin.law p) = ∫⁻ b, F b ∂RealCoin.law (callbackBias m p) := by
  cases m with
  | exp =>
    have h : firstCredit p .exp F = F := by funext b; cases b <;> rfl
    rw [h]
    rfl
  | cos => exact CoinProduct.expectation_preservation p p F
  | sinc => exact CoinProduct.expectation_preservation p p F

/-- Raw binders preserve the callback's free variables throughout the loop. -/
private def loop {rT : Type} (coin : Val rT) (m : Mode) (l : Loc) : Exp rT :=
  let bind (value body : Exp rT) := Exp.app (.lam body) value
  let again : Exp rT := pl% {Exp.bvar 10} ({Exp.bvar 9} + #1)
    ({Exp.bvar 8} * {Exp.bvar 0}) ({Exp.bvar 2} * {Exp.bvar 0})
    ({Exp.bvar 1} * {Exp.bvar 0}) {Exp.bvar 4}
  let scale : Exp rT := pl% if #int m.code = #0 then {Exp.bvar 8} + #1 else
    if #int m.code = #1 then (#2 * {Exp.bvar 8} + #1) * (#2 * {Exp.bvar 8} + #2)
    else (#2 * {Exp.bvar 8} + #2) * (#2 * {Exp.bvar 8} + #3)
  let compare (x : Exp rT) :=
    .app (.app (.app Occil.uniformBagLess (.lit (.loc l))) x) (.bvar 7)
  let branch := .cond (compare (.bvar 1)) pl(#true)
    (.cond (compare (.bvar 0)) (bind scale again) pl(#false))
  let hi : Exp rT := pl% if {Exp.bvar 7} % #2 = #0 then
    {Exp.bvar 5} + {Exp.bvar 1} else {Exp.bvar 4}
  let lo : Exp rT := pl% if {Exp.bvar 6} % #2 = #1 then
    {Exp.bvar 3} - {Exp.bvar 0} else {Exp.bvar 4}
  let term := Exp.cond (.bvar 0) pl(#1) pl(#0)
  let next := Exp.cond (.bvar 0) (grouped coin m) pl(#false)
  .fix (.lam (.lam (.lam (.lam (.lam (bind next (bind term (bind lo (bind hi branch)))))))))

private theorem grouped_lc {rT : Type} (coin : Val rT) (m : Mode) :
    (grouped coin m).IsLocallyClosed := by unfold grouped; is_lc

private theorem grouped_openRec {rT : Type} (coin : Val rT) (m : Mode)
    (k : ℕ) (e : Exp rT) : Exp.openRec k e (grouped coin m) = grouped coin m :=
  (Exp.open_lc k e _ (grouped_lc coin m)).symm

private def lowerValue (n lo hi : ℤ) (b : Bool) : ℤ :=
  if n % 2 = 1 then hi - (if b then 1 else 0) else lo

private def upperValue (n lo hi : ℤ) (b : Bool) : ℤ :=
  if n % 2 = 0 then lo + (if b then 1 else 0) else hi

private def factorExpression {rT : Type} (m : Mode) (n : ℤ) : Exp rT := pl%
  if #int m.code = #0 then #int n + #1 else
    if #int m.code = #1 then (#2 * #int n + #1) * (#2 * #int n + #2)
    else (#2 * #int n + #2) * (#2 * #int n + #3)

private theorem factorExpression_openRec {rT : Type} (m : Mode) (n : ℤ)
    (k : ℕ) (e : Exp rT) : Exp.openRec k e (factorExpression m n) = factorExpression m n :=
  (Exp.open_lc k e _ (by unfold factorExpression; is_lc)).symm

private def retryExpression {rT : Type} (self : Val rT) (m : Mode)
    (n d lo hi : ℤ) (b : Bool) : Exp rT :=
  .app (.lam (pl% &self.fst (#int n + #1) (#int d * {Exp.bvar 0})
    (#int lo * {Exp.bvar 0}) (#int hi * {Exp.bvar 0}) #bool b))
    (factorExpression m n)

private def prepared {rT : Type} (less self : Val rT) (l : Loc) (m : Mode)
    (n d lo hi : ℤ) (b : Bool) : Exp rT :=
  let lo' := lowerValue n lo hi b
  let hi' := upperValue n lo hi b
  .cond pl(&less.fst #loc l #int lo' #int d) pl(#true)
    (.cond pl(&less.fst #loc l #int hi' #int d) (retryExpression self m n d lo' hi' b) pl(#false))

private def afterGroup {rT : Type} (less self : Val rT) (l : Loc) (m : Mode)
    (n d lo hi : ℤ) (b : Bool) : Exp rT :=
  let bind (v body : Exp rT) := Exp.app (.lam body) v
  let again : Exp rT := pl% &self.fst (#int n + #1) (#int d * {Exp.bvar 0})
    ({Exp.bvar 2} * {Exp.bvar 0}) ({Exp.bvar 1} * {Exp.bvar 0}) #bool b
  let compare (x : Exp rT) := pl(&less.fst #loc l &x #int d)
  let branch := Exp.cond (compare (.bvar 1)) pl(#true)
    (.cond (compare (.bvar 0)) (bind (factorExpression m n) again) pl(#false))
  let upper : Exp rT := pl% if #int n % #2 = #0 then #int lo + {Exp.bvar 1} else #int hi
  let lower : Exp rT := pl% if #int n % #2 = #1 then #int hi - {Exp.bvar 0} else #int lo
  bind (Exp.cond pl(#bool b) pl(#1) pl(#0)) (bind lower (bind upper branch))

private theorem loop_lc {rT : Type} (coin : Val rT) (m : Mode) (l : Loc) :
    (loop coin m l).IsLocallyClosed := by
  unfold loop
  is_lc

private def loopValue {rT : Type} (coin : Val rT) (m : Mode) (l : Loc) : Val rT :=
  ⟨loop coin m l, .fix (loop_lc coin m l), loop_lc coin m l⟩

private def lessValue {rT : Type} : Val rT :=
  ⟨Occil.uniformBagLess, .fix UniformBag.uniformBagLess_lc, UniformBag.uniformBagLess_lc⟩

private theorem lowerValue_eq (m : Mode) (n : ℕ) (b : Bool) :
    lowerValue ((n + 1 : ℕ) : ℤ) (lowerNumerator m n) (upperNumerator m n) b =
      nextLower m n b := by
  have h : (((n + 1 : ℕ) : ℤ) % 2 = 1) ↔ (n + 1) % 2 = 1 := by omega
  simp only [lowerValue, nextLower, h]

private theorem upperValue_eq (m : Mode) (n : ℕ) (b : Bool) :
    upperValue ((n + 1 : ℕ) : ℤ) (lowerNumerator m n) (upperNumerator m n) b =
      nextUpper m n b := by
  have h : (((n + 1 : ℕ) : ℤ) % 2 = 0) ↔ (n + 1) % 2 = 0 := by omega
  simp only [upperValue, nextUpper, h]

private theorem int_beq {rT : Type} [BEq rT] (a b : ℤ) :
    ((BaseLit.int a : BaseLit rT) == .int b) = (a == b) := rfl

section specification

open Iris Iris.BI Iris.ProofMode TotalEris ErisWpGS

variable {rT : Type} [MeasurableSpace rT] [LawfulProbLangℝ rT]
  [ProbLangDist rT] [ProbLangDist.IsUniformInt rT] [ProbLangFFI rT] [ProbLangObs rT]
variable {hlc : HasLC} {GF : BundledGFunctors} [ErisGS rT hlc GF]
local bi (IProp GF)

omit [ProbLangDist.IsUniformInt rT] in
private theorem grouped_distSpec (E : CoPset) (p : unitInterval) (m : Mode) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E (grouped coin m) (RealCoin.law (callbackBias m p)) Val.bool where
  spec F hF := by
    iintro Hcredit
    twp_bind pl(&coin.fst #())
    isimp only [← grouped_expectation p m F] at Hcredit
    iapply (hcoin.wp (firstCredit p m F) (measurable_of_countable _) _) $$ Hcredit
    iintro %b Hcredit
    cases b
    · twp_pure
      twp_value
      imodintro
      iexists false
      isimp only [firstCredit, Bool.false_eq_true, ite_false] at Hcredit
      iframe Hcredit
      itrivial
    · twp_pure
      cases m with
      | exp =>
        twp_pures
        twp_value
        imodintro
        iexists true
        isimp only [firstCredit, ite_true] at Hcredit
        iframe Hcredit
        itrivial
      | cos =>
        twp_pures
        isimp only [firstCredit, ite_true, reduceCtorEq, ite_false] at Hcredit
        iapply hcoin.spec F hF $$ Hcredit
      | sinc =>
        twp_pures
        isimp only [firstCredit, ite_true, reduceCtorEq, ite_false] at Hcredit
        iapply hcoin.spec F hF $$ Hcredit

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_initialCall (E : CoPset) (self : Val rT) (m : Mode)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&self.fst #1 #int (initialDenominator m : ℤ) #0
      #int (initialDenominator m : ℤ) #true) Φ ⊢
        tglWp E (initialCall self m) Φ := by
  iintro H
  cases m
  all_goals
    twp_pures
    isimp only [initialDenominator] at H
    iexact H

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_prepare (E : CoPset) (less self : Val rT) (l : Loc) (m : Mode)
    (n d lo hi : ℤ) (b : Bool) (Φ : Val rT → IProp GF) :
    tglWp E (prepared less self l m n d lo hi b) Φ ⊢
      tglWp E (afterGroup less self l m n d lo hi b) Φ := by
  by_cases hn : n % 2 = 1
  · have he : n % 2 ≠ 0 := by omega
    have hlo : (n % 2 == 1) = true := beq_iff_eq.mpr hn
    have hhi : (n % 2 == 0) = false := beq_eq_false_iff_ne.mpr he
    cases b <;> iintro H
    all_goals
      twp_pures
      simp only [int_beq, hlo]
      twp_pures
      simp only [int_beq, hhi]
      twp_pures
      simp only [factorExpression_openRec]
      isimp only [prepared, retryExpression, lowerValue, upperValue, hn, he,
        Bool.false_eq_true, ite_true, ite_false, one_ne_zero] at H
      iexact H
  · have he : n % 2 = 0 := by omega
    have hlo : (n % 2 == 1) = false := beq_eq_false_iff_ne.mpr hn
    have hhi : (n % 2 == 0) = true := beq_iff_eq.mpr he
    cases b <;> iintro H
    all_goals
      twp_pures
      simp only [int_beq, hlo]
      twp_pures
      simp only [int_beq, hhi]
      twp_pures
      simp only [factorExpression_openRec]
      isimp only [prepared, retryExpression, lowerValue, upperValue, hn, he,
        Bool.false_eq_true, ite_true, ite_false, zero_ne_one] at H
      iexact H

private theorem state_den_pos (m : Mode) (n : ℕ) :
    (0 : ℤ) < stateDenominator m n := by exact_mod_cast denominator_pos m (n + 1)

omit [ProbLangDist.IsUniformInt rT] in
private theorem twp_retry (E : CoPset) (self : Val rT) (m : Mode) (n : ℕ)
    (Φ : Val rT → IProp GF) :
    tglWp E pl(&self.fst #int ((n + 1 + 1 : ℕ) : ℤ)
      #int (stateDenominator m (n + 1) : ℤ) #int (lowerNumerator m (n + 1))
      #int (upperNumerator m (n + 1)) #true) Φ ⊢
        tglWp E (retryExpression self m ((n + 1 : ℕ) : ℤ) (stateDenominator m n)
          (nextLower m n true) (nextUpper m n true) true) Φ := by
  have hd : (stateDenominator m (n + 1) : ℤ) =
      (stateDenominator m n : ℤ) * factor m (n + 1) := by
    exact_mod_cast denominator_succ m (n + 1)
  iintro H
  isimp only [hd, ← nextLower_true m n, ← nextUpper_true m n] at H
  cases m
  all_goals
    twp_pures
    isimp [factor] at H
    isimp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Exp.ofVal]
    iexact H

private def draw (coin : Val rT) (m : Mode) (l : Loc) (n : ℕ) : Exp rT :=
  pl(&(loop coin m l) #int ((n + 1 : ℕ) : ℤ) #int (stateDenominator m n : ℤ)
    #int (lowerNumerator m n) #int (upperNumerator m n) #true)

private theorem twp_round (E : CoPset) (p : unitInterval) (m : Mode) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (l : Loc) (N n : ℕ) (F : Bool → ℝ≥0∞)
    (hcontinue : ∀ q : List Bool,
      DyadicPosterior.resolves q (lower m (n + 1)) false →
      DyadicPosterior.resolves q (upper m (n + 1)) true →
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (horizonCredit m p (N + 1) (n + 1) F))) ⊢
          tglWp E (draw coin m l (n + 1))
            (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))))
    (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit m p (N + 1) n F))) ⊢
      tglWp E (draw coin m l n)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro ⟨Hbag, Hcredit⟩
  twp_pures
  simp only [UniformBag.uniformBagLess_openRec, grouped_openRec]
  twp_bind (grouped coin m)
  isimp only [← expectation m p q (N + 1) n F] at Hcredit
  iapply ((grouped_distSpec E p m coin hcoin).wp
    (fun b => DyadicPosterior.credit q (branchCredit m p (N + 1) n F b))
    (measurable_of_countable _) _) $$ Hcredit
  iintro %b Hcredit
  twp_pure
  simp only [UniformBag.uniformBagLess_openRec, grouped_openRec]
  ieval (
    change _ ⊢ tglWp E
      (afterGroup lessValue (loopValue coin m l) l m ((n + 1 : ℕ) : ℤ)
      (stateDenominator m n) (lowerNumerator m n) (upperNumerator m n) b) _)
  iapply twp_prepare E lessValue (loopValue coin m l) l m ((n + 1 : ℕ) : ℤ)
    (stateDenominator m n) (lowerNumerator m n) (upperNumerator m n) b
  isimp only [prepared, lowerValue_eq, upperValue_eq, lessValue]
  ieval (
    change _ ⊢ tglWp E
      (UniformBag.bracket l (nextLower m n b) (stateDenominator m n)
        (nextUpper m n b) (stateDenominator m n) pl(#true) pl(#false)
        (retryExpression (loopValue coin m l) m ((n + 1 : ℕ) : ℤ) (stateDenominator m n)
          (nextLower m n b) (nextUpper m n b) b)) _)
  iapply UniformBag.twp_bracket E l q _ _ _ _ (state_den_pos m n) (state_den_pos m n)
    (branchCredit m p (N + 1) n F b) (measurable_branchCredit m p (N + 1) n F b)
    pl(#true) pl(#false) _ _ ?_ ?_ ?_
  · intro r _ hlo
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists true
    ihave Hcredit := ErrorCredit.weaken (branch_lower_credit m p (N + 1) n r F b
      (by simpa only [Int.cast_natCast] using hlo)) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r _ _ hhi
    iintro ⟨Hbag, Hcredit⟩
    twp_value
    imodintro
    iexists false
    ihave Hcredit := ErrorCredit.weaken (branch_upper_credit m p (N + 1) n r F b
      (by simpa only [Int.cast_natCast] using hhi)) $$ Hcredit
    iframe Hcredit
    itrivial
  · intro r _ hlo hhi
    iintro ⟨Hbag, Hcredit⟩
    obtain ⟨rfl, hlo, hhi⟩ := retry_resolves m n r b
      (by simpa only [Int.cast_natCast] using hlo)
      (by simpa only [Int.cast_natCast] using hhi)
    isimp only [branchCredit, ite_true] at Hcredit
    iapply twp_retry E (loopValue coin m l) m n
    have hc := hcontinue r hlo hhi
    simp only [draw] at hc
    isimp only [loopValue]
    iapply hc
    iframe Hbag Hcredit
  · iframe Hbag Hcredit

private theorem twp_until (E : CoPset) (p : unitInterval) (m : Mode) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (l : Loc) (N n : ℕ) (hn : n ≤ N) (F : Bool → ℝ≥0∞) (q : List Bool) :
    iprop(UniformBag.owns l q ∗ ↯ (DyadicPosterior.credit q (horizonCredit m p (N + 1) n F))) ⊢
      tglWp E (draw coin m l n)
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  have hall : ∀ n ≤ N, ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (horizonCredit m p (N + 1) n F))) ⊢
          tglWp E (draw coin m l n)
            (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
    intro n hn
    apply Nat.decreasingInduction (motive := fun n _ => ∀ q : List Bool,
      iprop(UniformBag.owns l q ∗
        ↯ (DyadicPosterior.credit q (horizonCredit m p (N + 1) n F))) ⊢
          tglWp E (draw coin m l n)
            (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b)))) ?_ ?_ hn
    · intro n _ IH q
      iapply twp_round E p m coin hcoin l N n F (fun q _ _ => IH q) q
    · intro q
      iapply twp_round E p m coin hcoin l N N F ?_ q
      intro q hlo hhi
      iintro ⟨Hbag, Hcredit⟩
      iexfalso
      iapply ErrorCredit.contradict (unresolved_credit m p (N + 1) q F hlo hhi) $$ Hcredit
  exact hall n hn q

/-- Exact exp, cosine, and sinc factories, including both endpoint biases. -/
theorem twp_factorialSeriesFactory (E : CoPset) (p : unitInterval) (m : Mode) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool)
    (F : Bool → ℝ≥0∞) :
    ⊢ ↯ (RealCoin.credit (bias m p) F) -∗
      tglWp E pl(&Occil.factorialSeriesFactory &coin.fst #int m.code #())
        (fun v : Val rT => iprop(∃ b : Bool, ⌜v = Val.bool b⌝ ∗ ↯ (F b))) := by
  iintro Hcredit
  iapply twp_err_pos solve_not_value
  iintro %δ %hδ Hterm
  obtain ⟨N, hN⟩ := exists_horizon m p F δ hδ
  simp only [meanBias_eq] at hN
  icombine Hcredit Hterm as Htotal
  ihave Hcredit := ErrorCredit.weaken hN $$ Htotal
  isimp [Occil.factorialSeriesFactory, Exp.close, Exp.closeRec,
    UniformBag.uniformBagLess_closeRec, newBag_closeRec]
  twp_pures
  rw [mode_guard m]
  twp_pure
  simp only [newBag_openRec]
  twp_bind pl(&Occil.newUniformBag #())
  iapply tglWp_wand
  isplitl []
  · iapply UniformBag.twp_newUniformBag E
  iintro %v ⟨%l, %hv, Hbag⟩
  subst v
  twp_pure
  simp only [UniformBag.uniformBagLess_openRec]
  ieval (
    change _ ⊢ tglWp E (initialCall (loopValue coin m l) m) _)
  iapply twp_initialCall E (loopValue coin m l) m
  have hloop := twp_until (rT := rT) (GF := GF) E p m coin hcoin l N 0 (Nat.zero_le _) F []
  simp only [draw, lowerNumerator_zero, upperNumerator_zero, initial_denominator] at hloop
  isimp only [loopValue]
  iapply hloop
  iframe Hbag Hcredit

theorem factorialSeriesFactory_distSpec (E : CoPset) (p : unitInterval) (m : Mode) (coin : Val rT)
    (hcoin : IsDistSpec (GF := GF) E pl(&coin.fst #()) (RealCoin.law p) Val.bool) :
    IsDistSpec (GF := GF) E pl(&Occil.factorialSeriesFactory &coin.fst #int m.code #())
      (RealCoin.law (bias m p)) Val.bool where
  spec F _ := by
    simpa only [RealCoin.lintegral_law] using
      wand_entails (twp_factorialSeriesFactory E p m coin hcoin F)

end specification

end

end SampLib.FactorialSeriesFactory
