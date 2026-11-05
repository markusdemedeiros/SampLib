import Samplers.PSRN.Core

/-!
# Exact arithmetic on lazy random reals

Arithmetic preserves the shared latent operands. Rational intervals are
refined only when an observation or comparison needs more precision.
-/

namespace Occil.PSRN

open ProbLang

variable {rT : Type _}

@[pl_fold] def negate : Exp rT := pl%
  fun source, fun bits,
    let a := source bits;
    let range := snd(a);
    (-(fst(range)), (-(fst(a)), snd(range)))

@[pl_fold] def add : Exp rT := pl%
  fun left right, fun bits,
    let a := left bits;
    let b := right bits;
    let ar := snd(a);
    let br := snd(b);
    ((fst(a)) * (snd(br)) + (fst(b)) * (snd(ar)),
      ((fst(ar)) * (snd(br)) + (fst(br)) * (snd(ar)),
        (snd(ar)) * (snd(br))))

@[pl_fold] def subtract : Exp rT := pl%
  fun left right, &add left (&negate right)

@[pl_fold] def scaleRational : Exp rT := pl%
  fun source numerator denominator,
    if denominator <= #0 then fail else fun bits,
      let a := source bits;
      let range := snd(a);
      if numerator < #0 then
        ((fst(range)) * numerator, ((fst(a)) * numerator, (snd(range)) * denominator))
      else
        ((fst(a)) * numerator, ((fst(range)) * numerator, (snd(range)) * denominator))

/-- Interval multiplication also works when the operands share latent digits. -/
@[pl_fold] def multiply : Exp rT := pl%
  fun left right, fun bits,
    let a := left bits;
    let b := right bits;
    let ar := snd(a);
    let br := snd(b);
    let minimum := (fun x y, if x < y then x else y);
    let maximum := (fun x y, if x < y then y else x);
    let aa := (fst(a)) * (fst(b));
    let ab := (fst(a)) * (fst(br));
    let ba := (fst(ar)) * (fst(b));
    let bb := (fst(ar)) * (fst(br));
    (minimum (minimum aa ab) (minimum ba bb),
      (maximum (maximum aa ab) (maximum ba bb), (snd(ar)) * (snd(br))))

@[pl_fold] def reciprocal : Exp rT := pl%
  fun source, fun bits,
    let refine := (rec invert precision :=
      let a := source precision;
      let range := snd(a);
      let lo := fst(a);
      let hi := fst(range);
      let denominator := snd(range);
      if (lo = #0) && (hi = #0) then fail else
      if (lo <= #0) && (#0 <= hi) then invert (precision + #1) else
        (denominator * lo, (denominator * hi, lo * hi)));
    refine bits

@[pl_fold] def divide : Exp rT := pl%
  fun numerator denominator, &multiply numerator (&reciprocal denominator)

@[pl_fold] def integerPowerReal : Exp rT := pl%
  rec power source n :=
    if n < #0 then fail else if n = #0 then &rational #1 #1 else
    if n = #1 then source else
      let half := power source (n / #2);
      let square := &multiply half half;
      if n % #2 = #0 then square else &multiply source square

/-- Positive n-th root by rational bisection; no numerical transcendental
primitive is used. The source must be nonnegative, n must be positive. -/
@[pl_fold] def root : Exp rT := pl%
  fun source n,
    if n <= #0 then fail else if n = #1 then source else fun bits,
      if bits < #0 then fail else
        let denominator := &integerPower #2 bits;
        let denominatorPower := &integerPower denominator n;
        let below := (fun bound,
          let numeratorPower := &integerPower bound n;
          &less source (&rational numeratorPower denominatorPower));
        let bracket := (rec expand hi :=
          if below hi then hi else expand (hi * #2));
        let hi := bracket denominator;
        let bisect := (rec search lo hi :=
          if hi - lo <= #1 then (lo, (hi, denominator)) else
            let mid := (lo + hi) / #2;
            if below mid then search lo mid else search mid hi);
        bisect #0 hi

/-- Rational powers of a positive lazy real, including negative exponents. -/
@[pl_fold] def powerRational : Exp rT := pl%
  fun source numerator denominator,
    if denominator <= #0 then fail else
      if numerator = #0 then &rational #1 #1 else
      if numerator < #0 then
        &reciprocal (&root (&integerPowerReal source (-numerator)) denominator)
      else &root (&integerPowerReal source numerator) denominator

@[pl_fold] def minimum : Exp rT := pl%
  fun left right, if &less left right then left else right

@[pl_fold] def maximum : Exp rT := pl%
  fun left right, if &less left right then right else left

end Occil.PSRN
