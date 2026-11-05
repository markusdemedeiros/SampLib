import Samplers.Discrete.Combinatorics
import Samplers.Discrete

/-!
# Exact binomial algorithms

Fair-bit counting, envelope rejection, and binary decomposition of rational probabilities.

Sources: Occil's `randomfunc.html`, `randomgen.py`, and `randmisc.html`.
The existing `Occil.DiscreteExtra` namespace is retained for compatibility.
-/
namespace Occil.DiscreteExtra

open ProbLang

variable {rT : Type _}

/-- One uniform integer supplies n fair bits; count its set bits. -/
@[pl_fold] def binomialHalfBits : Exp rT := pl%
  fun n,
    if n < #0 then fail else
      let word := &Occil.uniformInt (&integerPower #2 n);
      let count := (rec go bits total :=
        if bits = #0 then total else go (bits / #2) (total + bits % #2));
      count word #0

/-- Bringmann's exact envelope-rejection algorithm for Binomial(n,1/2).
The acceptance probability uses integer binomial coefficients, not log-gamma. -/
@[pl_fold] def binomialHalfRejection : Exp rT := pl%
  rec sampleHalf n :=
    if n < #0 then fail else if n < #4 then &binomialHalfBits n else
    if n % #2 = #1 then
      sampleHalf (n - #1) + &Occil.uniformInt #2
    else
      let width := &integerSqrt n + #1;
      let loop := (rec draw u :=
        let block := &Occil.geometric &Occil.fairCoin #();
        let offset := block * width + &Occil.uniformInt width;
        let candidate := (if &Occil.fairCoin #() then n / #2 + offset
                          else n / #2 - offset - #1);
        if (candidate < #0) || (n < candidate) then draw #() else
          let numerator := &choose n candidate * width;
          let denominator := &integerPower #2 (n + #2 - block);
          if &Occil.rationalCoin numerator denominator then candidate else draw #());
      loop #()

/-- Farach-Colton–Tsai binary expansion of the rational success probability.
The half-binomial kernel uses the exact fair-bit construction. -/
@[pl_fold] def binomialBinary : Exp rT := pl%
  fun n numerator denominator,
    if (n < #0) || (denominator <= #0) || (numerator < #0) || (denominator < numerator)
    then fail else if numerator = denominator then n else
      let loop := (rec go remaining remainder successes :=
        if (remaining = #0) || (remainder = #0) then successes else
          let half := &binomialHalfBits remaining;
          let twice := #2 * remainder;
          if denominator <= twice then
            go (remaining - half) (twice - denominator) (successes + half)
          else go half twice successes);
      loop n numerator #0

end Occil.DiscreteExtra
