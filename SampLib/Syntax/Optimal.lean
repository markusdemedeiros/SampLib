import SampLib.WeightedIntegerPower
import SampLib.BitLength
import SampLib.ListEncoding
import Samplers.Weighted.Optimal

/-! # Closed auxiliary loops from the finite cyclic probability-matrix sampler -/

open ProbLang

namespace SampLib.Optimal.Program

@[pl_fold] def parameters {rT : Type} (k total : ℕ) : Exp rT := pl%
  rec select l bestL bestTotal :=
    if #int (k : ℤ) <= l then (bestL, bestTotal) else
      let denominator := #int ((2 ^ k : ℕ) : ℤ) - &Occil.Weighted.integerPower #2 l;
      if denominator = #int (total : ℤ) then (l, denominator) else
      if denominator < #int (total : ℤ) then (bestL, bestTotal)
      else select (l + #1) l denominator

@[pl_fold] def append {rT : Type} (rejected : ℕ) : Exp rT := pl%
  rec addLast xs := case! xs
    | inl(v) => inr((#int (rejected : ℤ), inl(#())))
    | inr(p) => inr(((fst(p)), addLast (snd(p))))

@[pl_fold] def encode {rT : Type} (k l denominator : ℕ) : Exp rT := pl%
  rec convert xs := case! xs
    | inl(v) => inl(#())
    | inr(p) =>
      let m := fst(p);
      let period := &Occil.Weighted.integerPower #2 (#int (k : ℤ) - #int (l : ℤ));
      let encoded := (if m = #int (denominator : ℤ) then #int ((2 ^ k : ℕ) : ℤ) - #1 else
        if #int (l : ℤ) = #int (k : ℤ) then m else if #int (l : ℤ) = #0 then m else
        (m / (period - #1)) * period + m % (period - #1));
      inr((encoded, convert (snd(p))))

@[pl_fold] def scan {rT : Type} : Exp rT := pl%
  rec search xs digit position index := case! xs
    | inl(v) => (#false, digit)
    | inr(p) =>
      let bit := (fst(p) / &Occil.Weighted.integerPower #2 position) % #2;
      let next := digit - bit;
      if next < #0 then (#true, index)
      else search (snd(p)) next position (index + #1)

@[pl_fold] def walk {rT : Type} [ProbLangℝ rT] (rows : List ℕ) (k l : ℕ)
    (rejected : ℤ) : Exp rT := pl%
  rec draw value column :=
    let expanded := #2 * value + rand(#2, #());
    let outcome := &scan &(listVal (fun n : ℕ => Val.int n) rows).fst expanded
      (#int (k : ℤ) - #1 - column) #0;
    if fst(outcome) then
      if snd(outcome) = #int rejected then draw #0 #0 else snd(outcome)
    else draw (snd(outcome))
      (if column + #1 = #int (k : ℤ) then #int (l : ℤ) else column + #1)

private instance integerPower_closed {rT : Type} :
    ClosedExp (Occil.Weighted.integerPower : Exp rT) where
  lc := WeightedIntegerPower.integerPower_lc
  fv := WeightedIntegerPower.integerPower_fv

instance parameters_closed {rT : Type} (k total : ℕ) :
    ClosedExp (parameters k total : Exp rT) where
  lc := by is_lc
  fv := by simp [parameters, Exp.fv, WeightedIntegerPower.integerPower_fv]

instance append_closed {rT : Type} (rejected : ℕ) :
    ClosedExp (append rejected : Exp rT) where
  lc := by is_lc
  fv := by simp [append, Exp.fv]

instance encode_closed {rT : Type} (k l denominator : ℕ) :
    ClosedExp (encode k l denominator : Exp rT) where
  lc := by is_lc
  fv := by simp [encode, Exp.fv, WeightedIntegerPower.integerPower_fv]

instance scan_closed {rT : Type} : ClosedExp (scan : Exp rT) where
  lc := by is_lc
  fv := by simp [scan, Exp.fv, WeightedIntegerPower.integerPower_fv]

end SampLib.Optimal.Program
