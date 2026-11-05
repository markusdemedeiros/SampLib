import Samplers.Weighted.Uniform

/-! # Bounded-integer reduction methods

Object-language algorithms from Occil’s uniform-integer and weighted-choice
comparisons. Lists use `inl(unit)` and `inr((head, tail))`.
-/

/-! ## Explicitly biased fixed-bit reductions. -/
namespace Occil.Weighted

open ProbLang
variable {rT : Type _}

/-- Approximate modulo reduction. Bias is present unless n divides 2^bits. -/
@[pl_fold] def moduloReduction : Exp rT := pl%
  fun n bits,
    if (n <= #0) || (bits < #0) then fail else
      &randomBits bits % n

/-- Approximate multiply-and-shift reduction, with an explicit input bit count. -/
@[pl_fold] def multiplyShift : Exp rT := pl%
  fun n bits,
    if (n <= #0) || (bits < #0) then fail else
      (&randomBits bits * n) / &integerPower #2 bits

/-! ## Exact word reductions and emulated floating-point multiplication. -/

end Occil.Weighted

namespace Occil.WeightedVariants

open ProbLang
variable {rT : Type _}

/-- Lemire multiply-high reduction with exact rejection of the biased low tail.
Requires 0<n<=2^bits. Multiplication is unbounded, so both word halves are retained. -/
@[pl_fold] def lemireUniform : Exp rT := pl%
  fun n bits,
    let modulus := &Weighted.integerPower #2 bits;
    if (n <= #0) || (modulus < n) then fail else
      let threshold := modulus % n;
      let loop := (rec draw u :=
        let product := n * &Weighted.randomBits bits;
        if product % modulus < threshold then draw #() else product / modulus);
      loop #()

/-- Round a nonnegative integer to a binary significand of the requested
precision, with round-to-nearest/ties-to-even. The exponent is unbounded. -/
@[pl_fold] def roundBinary : Exp rT := pl%
  fun value precision,
    if (value < #0) || (precision <= #0) then fail else
      let length := &bitLength value;
      if length <= precision then value else
        let quantum := &Weighted.integerPower #2 (length - precision);
        let significand := value / quantum;
        let remainder := value % quantum;
        let up := ((quantum < #2 * remainder) ||
          ((quantum = #2 * remainder) && (significand % #2 = #1)));
        (if up then significand + #1 else significand) * quantum

/-- O'Neill's biased floating-point multiply, emulated with integer arithmetic.
The significand precision must be at least the source-word width, so converting
that word to a floating value is exact. Rounding of the subsequent product is
explicit; no interpreter Float primitive or FFI is used. -/
@[pl_fold] def floatingMultiply : Exp rT := pl%
  fun n bits precision,
    let modulus := &Weighted.integerPower #2 bits;
    if (n <= #0) || (modulus < n) || (precision < bits) then fail else
      &roundBinary (n * &Weighted.randomBits bits) precision / modulus

/-- Division-with-rejection reduction from O'Neill's comparison. -/
@[pl_fold] def divisionRejection : Exp rT := pl%
  fun n bits,
    let modulus := &Weighted.integerPower #2 bits;
    if (n <= #0) || (modulus < n) then fail else
      let divisor := modulus / n;
      let loop := (rec draw u :=
        let value := &Weighted.randomBits bits / divisor;
        if value < n then value else draw #());
      loop #()

/-- OpenBSD's debiased modulo: discard the incomplete low interval. -/
@[pl_fold] def debiasedModulo : Exp rT := pl%
  fun n bits,
    let modulus := &Weighted.integerPower #2 bits;
    if (n <= #0) || (modulus < n) then fail else
      let threshold := modulus % n;
      let loop := (rec draw u :=
        let value := &Weighted.randomBits bits;
        if value < threshold then draw #() else value % n);
      loop #()

/-- O'Neill's conclusion variant of Lemire: avoid computing the threshold
unless the first product's low word is smaller than the requested range. -/
@[pl_fold] def oneillUniform : Exp rT := pl%
  fun n bits,
    let modulus := &Weighted.integerPower #2 bits;
    if (n <= #0) || (modulus < n) then fail else
      let product := n * &Weighted.randomBits bits;
      if product % modulus < n then
        let base := modulus - n;
        let threshold := (if base < n then base else
          let reduced := base - n;
          if reduced < n then reduced else reduced % n);
        let loop := (rec accept current :=
          if current % modulus < threshold then
            accept (n * &Weighted.randomBits bits)
          else current / modulus);
        loop product
      else product / modulus

end Occil.WeightedVariants
