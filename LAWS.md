# Sampler laws

[Implementations](code/README.md) · [Verified suite](SampLib/README.md)

588 sampler entries; 216 accepted proofs. **Verified** links identify accepted proofs; **draft** links are unreviewed. A dash means unverified. Domains and parameter conventions are in the code/proof.

$\mathrm{Geom}_0(p)$ counts failures. $\mathrm{Cat}(w)$ has masses $w_i/\sum_jw_j$. $\mathsf{Lazy}[D]$ denotes the intended latent law of a stateful real. $\mathsf{Grid}_s[D]$ labels a numerical algorithm targeting $D$; it does **not** claim its output is an exact or exactly rounded draw from $D$.

Unverified formulas describe intended laws, not established correctness. Removable singularities use the continuous extensions specified in the code. “Uncharacterized” records a missing law description rather than guessing one.

## Bernoulli factories / Basic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.bernoulliRace` | $\mathrm{Bern}\!\left(\frac{p}{p+q}\right)$ | Race two alternating coin trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L33) | [**verified**](SampLib/Samplers/BernoulliRace.lean) |
| `Occil.coinConditional` | $\mathrm{Bern}\!\left(rp+(1-r)q\right)$ | Compose callback and auxiliary coin trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L22) | [**verified**](SampLib/Samplers/CoinConditional.lean) |
| `Occil.coinDisjunction` | $\mathrm{Bern}\!\left(p+q-pq\right)$ | Compose callback and auxiliary coin trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L16) | [**verified**](SampLib/Samplers/CoinDisjunction.lean) |
| `Occil.coinMean` | $\mathrm{Bern}\!\left(\frac{p+q}{2}\right)$ | Compose callback and auxiliary coin trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L19) | [**verified**](SampLib/Samplers/CoinMean.lean) |
| `Occil.coinProduct` | $\mathrm{Bern}\!\left(pq\right)$ | Compose callback and auxiliary coin trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L13) | [**verified**](SampLib/Samplers/CoinProduct.lean) |
| `Occil.complement` | $\mathrm{Bern}\!\left(1-p\right)$ | Compose callback and auxiliary coin trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L11) | [**verified**](SampLib/Samplers/Complement.lean) |
| `Occil.evenParity` | $\mathrm{Bern}\!\left(\frac1{1+p}\right)$ | Parity of a geometric run | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L44) | [**verified**](SampLib/Samplers/EvenParity.lean) |
| `Occil.expMinusFactory` | $\mathrm{Bern}\!\left(e^{-p}\right)$ | Thinned decreasing-uniform chain | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L74) | [**verified**](SampLib/Samplers/ExpMinusFactory.lean) |
| `Occil.expMinusRational` | $\mathrm{Bern}\!\left(e^{-x/y}\right)$ | Alternating factorial-trial parity | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L60) | [**verified**](SampLib/Samplers/ExpMinusRational.lean) |
| `Occil.fractionalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | Mendo reciprocal-hazard trials | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L51) | — |
| `Occil.oneDivOnePlus` | $\mathrm{Bern}\!\left(\frac1{1+p}\right)$ | Two-outcome retry coin | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L39) | [**verified**](SampLib/Samplers/OneDivOnePlus.lean) |
| `Occil.vonNeumann` | $\mathrm{Bern}\!\left(\frac12\right)$ | Retry equal pairs of coin flips | [Basic.lean](code/Samplers/Bernoulli/Basic.lean#L26) | [**verified**](SampLib/Samplers/VonNeumann.lean) |
## Bernoulli factories / Combinators

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.bernsteinFactory` | $\mathrm{Bern}\!\left(\sum_{k=0}^n c_k\binom nk p^k(1-p)^{n-k}\right)$ | Binomial count selects rational coefficient | [Combinators.lean](code/Samplers/Bernoulli/Combinators.lean#L26) | [**verified**](SampLib/Samplers/BernsteinFactory.lean) |
| `Occil.logisticFactory` | $\mathrm{Bern}\!\left(\frac{xp}{y+xp}\right)$ | Weighted rational selector and retry | [Combinators.lean](code/Samplers/Bernoulli/Combinators.lean#L12) | [**verified**](SampLib/Samplers/LogisticFactory.lean) |
| `Occil.probabilityGeneratingFactory` | $\mathrm{Bern}\!\left(\mathbb E[p^N]\right)$ | Random count followed by all-success trials | [Combinators.lean](code/Samplers/Bernoulli/Combinators.lean#L19) | [**verified**](SampLib/Samplers/ProbabilityGeneratingFactory.lean) |
## Bernoulli factories / Elementary

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.complementHalf` | $\mathrm{Bern}\!\left(\frac{1-p}{2}\right)$ | (1-p)/2 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L124) | [**verified**](SampLib/Samplers/ComplementHalf.lean) |
| `Occil.FactoryExtra.complementLogInverse` | $\mathrm{Bern}\!\left((1-p)\log(1/(1-p))\right)$ | (1-p)*ln(1/(1-p)); requires p<1 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L97) | [**verified**](SampLib/Samplers/ComplementLogInverse.lean) |
| `Occil.FactoryExtra.complementLogOnePlus` | $\mathrm{Bern}(1-\log(1+p))$ | 1-ln(1+p) | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L128) | [**verified**](SampLib/Samplers/ComplementLogOnePlus.lean) |
| `Occil.FactoryExtra.complementOverLogInverse` | $\mathrm{Bern}\!\left(\frac{1-p}{\log(1/p)}\right)$ | (1-p)/ln(1/p), extended to one at p=1; p>0 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L107) | — |
| `Occil.FactoryExtra.expIntegral` | $\mathrm{Bern}\!\left(\frac{1-e^{-(m+p)}}{m+p}\right)$ | (1-exp(-(m+p)))/(m+p), with integer m>=0 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L71) | — |
| `Occil.FactoryExtra.exponentialRatio` | $\mathrm{Bern}\!\left(\frac{1+e^{z-w}}{1+e^z}\right)$ | (1+exp(z-w))/(1+exp(z)), z=a/b,w=x/y>=0 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L66) | [**verified**](SampLib/Samplers/ExponentialRatio.lean) |
| `Occil.FactoryExtra.exponentialTwist` | $\mathrm{Bern}\!\left(\frac{pe^z}{pe^z+1-p}\right)$ | Exponential shift p*exp(z)/(p*exp(z)+1-p), z=a/b | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L58) | [**verified**](SampLib/Samplers/ExponentialTwist.lean) |
| `Occil.FactoryExtra.logOverAffine` | $\mathrm{Bern}\!\left(\frac{\log(c+p)}{c+p}\right)$ | ln(c+p)/(c+p), c=a/b>=1, via the one-cycle permutation schema | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L83) | [**verified**](SampLib/Samplers/LogOverAffine.lean) |
| `Occil.FactoryExtra.logisticExp` | $\mathrm{Bern}\!\left(\frac1{1+e^{z/2^k}}\right)$ | LogisticExp(z,precision)=1-expit(z/2^precision) | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L38) | [**verified**](SampLib/Samplers/LogisticExp.lean) |
| `Occil.FactoryExtra.oneMinusOverOnePlus` | $\mathrm{Bern}\!\left(\frac{1-p}{1+p}\right)$ | (1-p)/(1+p), a uniformly-fast two-coin construction | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L16) | [**verified**](SampLib/Samplers/OneMinusOverOnePlus.lean) |
| `Occil.FactoryExtra.onePlusHalf` | $\mathrm{Bern}\!\left(\frac{1+p}{2}\right)$ | (1+p)/2 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L120) | [**verified**](SampLib/Samplers/OnePlusHalf.lean) |
| `Occil.FactoryExtra.pLogInverse` | $\mathrm{Bern}\!\left(p\log(1/p)\right)$ | Geometric count and reciprocal acceptance | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L91) | [**verified**](SampLib/Samplers/PLogInverse.lean) |
| `Occil.FactoryExtra.pOverLogInverseComplement` | $\mathrm{Bern}\!\left(\frac p{\log(1/(1-p))}\right)$ | p/ln(1/(1-p)), extended to one at p=0; p<1 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L101) | — |
| `Occil.FactoryExtra.polylogarithm` | $\mathrm{Bern}\!\left(\mathrm{Li}_r(p)(1/p-1)\right)$ | Li_r(p)*(1/p-1), integer r>=1, extended to one at p=0 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L113) | [**verified**](SampLib/Samplers/Polylogarithm.lean) |
| `Occil.FactoryExtra.sigmoidDerivative` | $\mathrm{Bern}\!\left(\sigma(z)(1-\sigma(z))\right)$ | expit(z)*(1-expit(z)), z=a/b | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L132) | [**verified**](SampLib/Samplers/SigmoidDerivative.lean) |
| `Occil.FactoryExtra.sigmoidRational` | $\mathrm{Bern}\!\left(\frac1{1+e^{-a/b}}\right)$ | expit(z), where z=a/b may have either sign | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L23) | [**verified**](SampLib/Samplers/SigmoidRational.lean) |
| `Occil.FactoryExtra.sigmoidScaled` | $\mathrm{Bern}\!\left(\frac1{1+e^{-ap/b}}\right)$ | expit((a/b)*p), with arbitrary signed rational a/b | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L31) | [**verified**](SampLib/Samplers/SigmoidScaled.lean) |
| `Occil.FactoryExtra.tanhHalfShifted` | $\mathrm{Bern}\!\left(\tanh((m+p)/2)\right)$ | tanh((m+p)/2), m=a/b>=0 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L53) | [**verified**](SampLib/Samplers/TanhHalfShifted.lean) |
| `Occil.FactoryExtra.tanhRational` | $\mathrm{Bern}\!\left(\tanh(a/b)\right)$ | tanh(a/b), a>=0,b>0, using exp(-2a/b) | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L43) | [**verified**](SampLib/Samplers/TanhRational.lean) |
| `Occil.FactoryExtra.tanhScaled` | $\mathrm{Bern}\!\left(\tanh(ap/b)\right)$ | tanh((a/b)*p), a>=0,b>0 | [Elementary.lean](code/Samplers/Bernoulli/Elementary.lean#L48) | [**verified**](SampLib/Samplers/TanhScaled.lean) |
## Bernoulli factories / Exponential

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.binaryExponential` | $\mathrm{Bern}\!\left(2^{-m(k+p)}\right)$ | 2^(-m*(k+p)), integers m,k>=0 | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L88) | — |
| `Occil.FactoryExtra.binaryExponentialRational` | $\mathrm{Bern}\!\left(2^{-ap/b}\right)$ | 2^(-(a/b)*p), a>=0,b>0 | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L98) | — |
| `Occil.FactoryExtra.expDivThree` | $\mathrm{Bern}\!\left(e^p/3\right)$ | exp(p)/3, from Poisson generating functions and the known e/3 coin | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L65) | — |
| `Occil.FactoryExtra.expMinusExp` | $\mathrm{Bern}\!\left(e^{-e^{m+p}}\right)$ | exp(-exp(m+p)), integer m>=0; Poisson thinning from the source recipe | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L72) | — |
| `Occil.FactoryExtra.expMinusPolynomial` | $\mathrm{Bern}\!\left(e^{-\sum_i a_ip^i}\right)$ | exp(-sum_i a_i*p^i), nonnegative rational coefficient pairs a_i | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L39) | [**verified**](SampLib/Samplers/ExpMinusPolynomial.lean) |
| `Occil.FactoryExtra.expMinusScaled` | $\mathrm{Bern}\!\left(e^{-cp}\right)$ | exp(-c*p), c=a/b>=0, by Poisson thinning | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L17) | [**verified**](SampLib/Samplers/ExpMinusScaled.lean) |
| `Occil.FactoryExtra.expMinusShiftPower` | $\mathrm{Bern}\!\left(e^{-(m+p)^k}\right)$ | exp(-(m+p)^k), integer m,k>=0, via its binomial polynomial expansion | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L52) | [**verified**](SampLib/Samplers/ExpMinusShiftPower.lean) |
| `Occil.FactoryExtra.expMinusShifted` | $\mathrm{Bern}\!\left(e^{-(m+p)}\right)$ | exp(-m-p), where m=a/b>=0 | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L23) | [**verified**](SampLib/Samplers/ExpMinusShifted.lean) |
| `Occil.FactoryExtra.expSquareTimesComplement` | $\mathrm{Bern}\!\left(e^{p^2}(1-p)\right)$ | exp(p^2)*(1-p), the factorial-pair alternating-series construction | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L82) | — |
| `Occil.FactoryExtra.expTimesComplement` | $\mathrm{Bern}\!\left(e^p(1-p)\right)$ | exp(p)*(1-p), the sorted-uniform von Neumann schema | [Exponential.lean](code/Samplers/Bernoulli/Exponential.lean#L28) | [**verified**](SampLib/Samplers/ExpTimesComplement.lean) |
## Bernoulli factories / Linear

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.addition` | $\mathrm{Bern}\!\left(p+q\right)$ | p+q, assuming p+q <= 1-e/f | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L63) | [**verified**](SampLib/Samplers/Addition.lean) |
| `Occil.FactoryExtra.division` | $\mathrm{Bern}\!\left(p/q\right)$ | q/p, assuming p-q >= e/f>0 | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L73) | [**verified**](SampLib/Samplers/Division.lean) |
| `Occil.FactoryExtra.epsilonDivision` | $\mathrm{Bern}\!\left(p/q\right)$ | eps/p with a known lower bound p>=lower>eps | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L78) | [**verified**](SampLib/Samplers/EpsilonDivision.lean) |
| `Occil.FactoryExtra.gambler` | $\mathrm{Bern}\!\left(\frac{\sum_{j=1}^{h-1}(cp)^j}{\sum_{j=0}^{h-1}(cp)^j}\right)$ | Finite gambler’s-ruin hitting probability | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L16) | [**verified**](SampLib/Samplers/Gambler.lean) |
| `Occil.FactoryExtra.highPowerLogistic` | $\mathrm{Bern}\!\left(\frac{(cp)^m}{\sum_{j=0}^m(cp)^j}\right)$ | High-power logistic walk, c^m*p^m/(1+cp+...+(cp)^m) | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L25) | [**verified**](SampLib/Samplers/HighPowerLogistic.lean) |
| `Occil.FactoryExtra.linear` | $\mathrm{Bern}\!\left(cp\right)$ | Exact expanding linear factory, (a/b)*p (Huber 2016) | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L35) | [**verified**](SampLib/Samplers/LinearFactory.lean) |
| `Occil.FactoryExtra.linear2014` | $\mathrm{Bern}\!\left(cp\right)$ | Huber 2014 expanding linear factory | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L129) | — |
| `Occil.FactoryExtra.linearLowProbability` | $\mathrm{Bern}\!\left(cp\right)$ | Low-probability linear factory; [known margin defect](agent-docs/reviews/ExpansionDomainFindings.md#low-probability-linear-wrapper) | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L93) | — |
| `Occil.FactoryExtra.linearPower` | $\mathrm{Bern}\!\left((cp)^m\right)$ | (c*p)^n, with the same margin condition as linear | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L57) | [**verified**](SampLib/Samplers/LinearPower.lean) |
| `Occil.FactoryExtra.linearPowerWalk` | $\mathrm{Bern}\!\left((cp)^m\right)$ | Huber 2019 joint linear-and-power factory, (c*p)^exponent | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L108) | — |
| `Occil.FactoryExtra.subtraction` | $\mathrm{Bern}\!\left(p-q\right)$ | p-q, assuming p-q >= e/f>0 | [Linear.lean](code/Samplers/Bernoulli/Linear.lean#L68) | [**verified**](SampLib/Samplers/Subtraction.lean) |
## Bernoulli factories / Polynomials

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.polynomial` | $\mathrm{Bern}\!\left(f(p)\right)$ | Polynomial evaluation through automatic Bernstein degree elevation | [Polynomials.lean](code/Samplers/Bernoulli/Polynomials.lean#L19) | — |
| `Occil.FactoryExtra.rationalFunction` | $\mathrm{Bern}\!\left(f(p)/g(p)\right)$ | A(p)/(A(p)+B(p)) with polynomial numerator/complement denominator | [Polynomials.lean](code/Samplers/Bernoulli/Polynomials.lean#L48) | — |
| `Occil.FactoryExtra.threePointPiecewise` | $\mathrm{Bern}(f(p)),\ f\text{ piecewise affine}$ | Three-point piecewise-affine coin construction | [Polynomials.lean](code/Samplers/Bernoulli/Polynomials.lean#L57) | — |
## Bernoulli factories / Powers

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.rationalPower` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | p^(a/b), a>=0,b>0, combining integer and fractional powers | [Powers.lean](code/Samplers/Bernoulli/Powers.lean#L15) | — |
| `Occil.FactoryExtra.twoCoin` | $\mathrm{Bern}\!\left(\frac{\beta xp}{\beta(xp+yq)+(1-\beta)(x+y)}\right)$ | Portkey two-coin race | [Powers.lean](code/Samplers/Bernoulli/Powers.lean#L35) | [**verified**](SampLib/Samplers/TwoCoin.lean) |
| `Occil.FactoryExtra.twoCoinPower` | $\mathrm{Bern}\!\left(p^q\right)$ | p^q with two unknown-probability input coins (Mendo's two-coin variant) | [Powers.lean](code/Samplers/Bernoulli/Powers.lean#L24) | — |
## Bernoulli factories / Rational

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.affine` | $\mathrm{Bern}\!\left(\frac{d+p}{c}\right)$ | (d+p)/c with rational d,c and an explicit margin when expansion is needed | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L27) | [**verified**](SampLib/Samplers/AffineFactory.lean) |
| `Occil.FactoryExtra.affineRatio` | $\mathrm{Bern}\!\left(\frac{d+q}{c+p}\right)$ | (d+q)/(c+p) | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L36) | [**verified**](SampLib/Samplers/AffineRatio.lean) |
| `Occil.FactoryExtra.inverseQuadratic` | $\mathrm{Bern}\!\left(\frac1{1+(m+p)^2}\right)$ | 1/(1+(m+p)^2), integer m>=0 | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L68) | [**verified**](SampLib/Samplers/InverseQuadratic.lean) |
| `Occil.FactoryExtra.oddsProduct` | $\mathrm{Bern}\!\left(\frac{\mu p}{1-\mu+\mu p}\right)$ | mu*p/(1-mu+mu*p), requiring mu<1 or p>0 | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L104) | [**verified**](SampLib/Samplers/OddsProduct.lean) |
| `Occil.FactoryExtra.offsetRace` | $\mathrm{Bern}\!\left(\frac{d+q}{c+p+d+q}\right)$ | (d+q)/(c+p+d+q), with nonnegative rational offsets c=a/b,d=x/y | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L83) | [**verified**](SampLib/Samplers/OffsetRace.lean) |
| `Occil.FactoryExtra.oneDivTwoMinus` | $\mathrm{Bern}\!\left(\frac1{2-p}\right)$ | Compose callback and auxiliary coin trials | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L64) | [**verified**](SampLib/Samplers/OneDivTwoMinus.lean) |
| `Occil.FactoryExtra.reciprocalAffine` | $\mathrm{Bern}\!\left(\frac d{c+p}\right)$ | d/(c+p), with c=a/b, d=x/y, 0<=d<=c, c>0 | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L15) | [**verified**](SampLib/Samplers/ReciprocalAffine.lean) |
| `Occil.FactoryExtra.reciprocalAffinePower` | $\mathrm{Bern}\!\left(\left(\frac d{c+p}\right)^k\right)$ | (d/(c+p))^k, with c=a/b,d=x/y | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L77) | [**verified**](SampLib/Samplers/ReciprocalAffinePower.lean) |
| `Occil.FactoryExtra.reciprocalExpAffine` | $\mathrm{Bern}\!\left(\frac1{c+e^{-z}}\right)$ | 1/(c+exp(-z)), c=a/b>=1,z=x/y>=0 | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L99) | [**verified**](SampLib/Samplers/ReciprocalExpAffine.lean) |
| `Occil.FactoryExtra.reciprocalLogistic` | $\mathrm{Bern}\!\left(\frac1{1+cp}\right)$ | Reciprocal logistic: 1/(1+(a/b)*p), a>=0,b>0 | [Rational.lean](code/Samplers/Bernoulli/Rational.lean#L60) | [**verified**](SampLib/Samplers/ReciprocalLogistic.lean) |
## Bernoulli factories / Series

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.alternatingSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}(-1)^nc_np^n\right)$ | An arbitrary rational-coefficient alternating power series | [Series.lean](code/Samplers/Bernoulli/Series.lean#L20) | — |
| `Occil.FactoryExtra.approximateFactory` | $\mathrm{Bern}\!\left(\mathbb E[\mathrm{clip}(f_s(\lfloor sK/N\rfloor),0,s)/s]\right)$ | A numerical plug-in factory | [Series.lean](code/Samplers/Bernoulli/Series.lean#L125) | [**verified**](SampLib/Samplers/ApproximateFactory.lean) |
| `Occil.FactoryExtra.complementPowerSeries` | $\mathrm{Bern}\!\left(1-\frac{\sum_i c_i(1-p)^{i+1}}{\sum_i c_i}\right)$ | Mendo power-series factory: 1-sum_i c_i*(1-p)^(i+1), normalized integer c_i | [Series.lean](code/Samplers/Bernoulli/Series.lean#L42) | [**verified**](SampLib/Samplers/ComplementPowerSeries.lean) |
| `Occil.FactoryExtra.convexCombination` | $\mathrm{Bern}\!\left(\frac{\sum_iw_ip_i}{\sum_iw_i}\right)$ | A finite mixture of coin callbacks, with nonnegative integer weights | [Series.lean](code/Samplers/Bernoulli/Series.lean#L59) | [**verified**](SampLib/Samplers/ConvexCombination.lean) |
| `Occil.FactoryExtra.envelopeFactory` | $\mathrm{Bern}\!\left(f(p)\right)$ | Consecutive-degree specialization of the general envelope algorithm | [Series.lean](code/Samplers/Bernoulli/Series.lean#L118) | — |
| `Occil.FactoryExtra.envelopeFactoryDegrees` | $\mathrm{Bern}\!\left(f(p)\right)$ | General reverse-time Bernstein-envelope factory with caller-selected degrees | [Series.lean](code/Samplers/Bernoulli/Series.lean#L79) | — |
| `Occil.FactoryExtra.integralMixture` | $\mathrm{Bern}\!\left(\int f(x)\,\mu(dx)\right)$ | Compose callback and auxiliary coin trials | [Series.lean](code/Samplers/Bernoulli/Series.lean#L67) | [**verified**](SampLib/Samplers/IntegralMixture.lean) |
| `Occil.FactoryExtra.minimumComplement` | $\mathrm{Bern}\!\left(\min(p,1-p)\right)$ | min(p,1-p), via Occil's Catalan-mixture Bernstein construction | [Series.lean](code/Samplers/Bernoulli/Series.lean#L135) | — |
| `Occil.FactoryExtra.minimumHalf` | $\mathrm{Bern}(\min(p,1/2))$ | Compose callback and auxiliary coin trials | [Series.lean](code/Samplers/Bernoulli/Series.lean#L150) | — |
| `Occil.FactoryExtra.positivePowerSeries` | $\mathrm{Bern}\!\left(\frac{\sum_i c_ip^i}{\sum_i c_i}\right)$ | Finite nonnegative power series, normalized by the integer coefficient sum | [Series.lean](code/Samplers/Bernoulli/Series.lean#L36) | [**verified**](SampLib/Samplers/PositivePowerSeries.lean) |
| `Occil.FactoryExtra.powerSeriesHazards` | $\mathrm{Bern}\!\left(1-\sum_{n\ge0}c_n(1-p)^{n+1}\right)$ | Compose callback and auxiliary coin trials | [Series.lean](code/Samplers/Bernoulli/Series.lean#L50) | — |
## Bernoulli factories / Trigonometric

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.alternatingPermutation` | $\mathrm{Bern}\!\left(\begin{cases}(1-p)/\cos p&r=0\\(1-p)\tan p&r=1\end{cases}\right)$ | Geometric count and alternating permutation test | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L47) | — |
| `Occil.FactoryExtra.arcsineHalf` | $\mathrm{Bern}\!\left(\frac12\arcsin p\right)$ | arcsin(p)/2, by cancelling the square-root component | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L81) | — |
| `Occil.FactoryExtra.arcsinePlusSqrtMinusOne` | $\mathrm{Bern}\!\left(\arcsin p+\sqrt{1-p^2}-1\right)$ | arcsin(p)+sqrt(1-p^2)-1 | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L69) | — |
| `Occil.FactoryExtra.arctanOverPi` | $\mathrm{Bern}\!\left(\arctan(p)/\pi\right)$ | arctan(p)/pi, with the exact known inverse-pi coin | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L32) | — |
| `Occil.FactoryExtra.complementOverCosine` | $\mathrm{Bern}\!\left(\frac{1-p}{\cos p}\right)$ | Compose callback and auxiliary coin trials | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L61) | — |
| `Occil.FactoryExtra.complementTimesTangent` | $\mathrm{Bern}\!\left((1-p)\tan p\right)$ | Compose callback and auxiliary coin trials | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L64) | — |
| `Occil.FactoryExtra.cosineSqrt` | $\mathrm{Bern}\!\left(\cos\sqrt p\right)$ | cos(sqrt(p)), an alternating power-series factory | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L26) | — |
| `Occil.FactoryExtra.pOverTangent` | $\mathrm{Bern}\!\left(\frac p{\tan p}\right)$ | p/tan(p), with an explicit valid lower bound e/f on sin(p)-p*cos(p) | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L88) | — |
| `Occil.FactoryExtra.sincScaled` | $\mathrm{Bern}\!\left(\frac{\sin(p\sqrt c)}{p\sqrt c}\right)$ | sin(p*sqrt(c))/(p*sqrt(c)), c=a/b in (0,6], extended to one at p=0 | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L17) | — |
| `Occil.FactoryExtra.sincSqrtScaled` | $\mathrm{Bern}\!\left(\frac{\sin\sqrt{cp}}{\sqrt{cp}}\right)$ | sin(sqrt(c*p))/sqrt(c*p), c=a/b in (0,6] | [Trigonometric.lean](code/Samplers/Bernoulli/Trigonometric.lean#L37) | — |
## Combinatorial sampling / Basic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.choice` | $\frac1n\sum_i\delta_{x_i}$ | Uniform position and list lookup | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L11) | [**verified**](SampLib/Samplers/Choice.lean) |
| `Occil.positiveComposition` | $\mathrm{Unif}\{x\in\mathbb N_{>0}^n:\sum_i x_i=t\}$ | Differences of uniformly chosen cut points | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L86) | [**verified**](SampLib/Samplers/PositiveComposition.lean) |
| `Occil.randomGraph` | $G(n,p)$ | Independent Bernoulli edge indicators | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L105) | [**verified**](SampLib/Samplers/RandomGraph.lean) |
| `Occil.reservoir` | $\mathrm{Unif}\{I\subseteq[n]:\#I=k\}\ \text{(unordered)}$ | Reservoir Algorithm R slot replacement | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L65) | [**verified**](SampLib/Samplers/Reservoir.lean) |
| `Occil.sampleInOrder` | $\mathrm{Unif}\{I\subseteq[n]:\#I=k\}$ | Sequential subset inclusion decisions | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L25) | [**verified**](SampLib/Samplers/SampleInOrder.lean) |
| `Occil.sampleWithReplacement` | $\left(\frac1n\sum_i\delta_{x_i}\right)^{\otimes k}$ | Repeat independent uniform position draws | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L14) | [**verified**](SampLib/Samplers/SampleWithReplacement.lean) |
| `Occil.sampleWithoutReplacement` | $\mathrm{Unif}(\text{ordered distinct positions})$ | Draw and remove a uniform position | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L17) | [**verified**](SampLib/Samplers/SampleWithoutReplacement.lean) |
| `Occil.shuffle` | $\mathrm{Unif}(S_n)$ | Fisher–Yates in-place swaps | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L47) | [**verified**](SampLib/Samplers/Shuffle.lean) |
| `Occil.weakComposition` | $\mathrm{Unif}\{x\in\mathbb N^n:\sum_i x_i=t\}$ | Shift a positive composition | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L95) | [**verified**](SampLib/Samplers/WeakComposition.lean) |
## Combinatorial sampling / Permutations

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.derangement` | $\mathrm{Unif}\{\pi\in S_n:\forall i,\pi(i)\ne i\}$ | Reject permutations having fixed points | [Permutations.lean](code/Samplers/Combinatorial/Permutations.lean#L30) | [**verified**](SampLib/Samplers/Derangement.lean) |
| `Occil.flipBits` | $(b_i\mathbin{\oplus}\mathrm{Bern}_i(p))_i$ | Independent input-bit flips | [Permutations.lean](code/Samplers/Combinatorial/Permutations.lean#L39) | [**verified**](SampLib/Samplers/FlipBits.lean) |
| `Occil.sattolo` | $\mathrm{Unif}(\text{single }n\text{-cycles})$ | Sattolo restricted in-place swaps | [Permutations.lean](code/Samplers/Combinatorial/Permutations.lean#L12) | [**verified**](SampLib/Samplers/Sattolo.lean) |
## Constant coins / Algebraic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.goldenFamily` | $\mathrm{Bern}\!\left(\left(\frac{m+\sqrt{m^2+4\ell}}2\right)^{-k}\right)$ | Exact G(m,ell)^(-k), G=(m+sqrt(m²+4ell))/2>1 | [Algebraic.lean](code/Samplers/Constants/Algebraic.lean#L30) | [**verified**](SampLib/Samplers/GoldenFamily.lean) |
| `Occil.Constants.inverseGoldenRatio` | $\mathrm{Bern}\!\left((\sqrt5-1)/2\right)$ | Exact inverse golden ratio, root of 1-x-x² | [Algebraic.lean](code/Samplers/Constants/Algebraic.lean#L19) | [**verified**](SampLib/Samplers/InverseGoldenRatio.lean) |
| `Occil.Constants.inverseSqrtTwo` | $\mathrm{Bern}\!\left(1/\sqrt2\right)$ | Exact rational-bound or series coin | [Algebraic.lean](code/Samplers/Constants/Algebraic.lean#L25) | [**verified**](SampLib/Samplers/InverseSqrtTwo.lean) |
| `Occil.Constants.sqrtTwoMinusOne` | $\mathrm{Bern}\!\left(\sqrt2-1\right)$ | Exact rational-bound or series coin | [Algebraic.lean](code/Samplers/Constants/Algebraic.lean#L22) | [**verified**](SampLib/Samplers/SqrtTwoMinusOne.lean) |
## Constant coins / Engines

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.algebraicRoot` | $\mathrm{Bern}\!\left(\alpha,\ f(\alpha)=0\right)$ | Random binary search using exact signs | [Engines.lean](code/Samplers/Constants/Engines.lean#L132) | [**verified**](SampLib/Samplers/AlgebraicRoot.lean) |
| `Occil.Constants.continuedFraction` | $\mathrm{Bern}\!\left(\cfrac1{a_1+\cfrac1{a_2+\cdots}}\right)$ | Positive simple continued fractions | [Engines.lean](code/Samplers/Constants/Engines.lean#L112) | [**verified**](SampLib/Samplers/ContinuedFraction.lean) |
| `Occil.Constants.continuedLogarithm` | $\mathrm{Bern}\!\left(\cfrac{2^{-c_1}}{1+\cfrac{2^{-c_2}}{1+\cdots}}\right)$ | Continued logarithm: (1/2^c₁)/(1+(1/2^c₂)/(1+...)) | [Engines.lean](code/Samplers/Constants/Engines.lean#L118) | — |
| `Occil.Constants.fromApproximateDigits` | $\mathrm{Bern}\!\left(p\right)$ | Refine approximate digits against random prefix | [Engines.lean](code/Samplers/Constants/Engines.lean#L30) | [**verified**](SampLib/Samplers/FromApproximateDigits.lean) |
| `Occil.Constants.fromBounds` | $\mathrm{Bern}\!\left(p\right)$ | Refine bounds against one cached uniform | [Engines.lean](code/Samplers/Constants/Engines.lean#L44) | [**verified**](SampLib/Samplers/FromBounds.lean) |
| `Occil.Constants.fromDigits` | $\mathrm{Bern}\!\left(\sum_{k\ge1}d_kb^{-k}\right)$ | Compare exact probability digits | [Engines.lean](code/Samplers/Constants/Engines.lean#L18) | [**verified**](SampLib/Samplers/FromDigits.lean) |
| `Occil.Constants.fromPositiveSeries` | $\mathrm{Bern}\!\left(\sum_{n\ge0}a_n/b_n\right)$ | Accumulate series with certified tail bounds | [Engines.lean](code/Samplers/Constants/Engines.lean#L59) | [**verified**](SampLib/Samplers/FromPositiveSeries.lean) |
| `Occil.Constants.generalizedContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1}{a_1+\cfrac{b_2}{a_2+\cdots}}\right)$ | Positive generalized continued fraction b₁/(a₁+b₂/(a₂+...)) | [Engines.lean](code/Samplers/Constants/Engines.lean#L84) | [**verified**](SampLib/Samplers/GeneralizedContinuedFraction.lean) |
| `Occil.Constants.rationalContinuedFraction` | $\mathrm{Bern}\!\left(\cfrac{b_1/d_1}{a_1/d_1+\cfrac{b_2/d_2}{a_2/d_2+\cdots}}\right)$ | Positive rational generalized continued fractions | [Engines.lean](code/Samplers/Constants/Engines.lean#L98) | — |
## Constant coins / Exponential

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.eContinuedFraction` | $\mathrm{Bern}(p_j),\ p_j\text{ a continued-fraction tail}$ | The article's continued-fraction expansion of 1/(e+c-2) | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L76) | — |
| `Occil.Constants.eDivThree` | $\mathrm{Bern}\!\left(e/3\right)$ | Exact rational-bound or series coin | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L44) | — |
| `Occil.Constants.eMinusTwo` | $\mathrm{Bern}\!\left(e-2\right)$ | Exact rational-bound or series coin | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L27) | — |
| `Occil.Constants.eMinusTwoContinuedFraction` | $\mathrm{Bern}\!\left(e-2\right)$ | Exact rational-bound or series coin | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L89) | — |
| `Occil.Constants.eQuarter` | $\mathrm{Bern}(e/4)$ | Exact rational-bound or series coin | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L131) | — |
| `Occil.Constants.eScaled` | $\mathrm{Bern}(en/d)$ | Exact Bernoulli(e*numerator/denominator), provided the result lies in [0,1] | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L34) | [**verified**](SampLib/Samplers/EScaled.lean) |
| `Occil.Constants.exponentialRationalProduct` | $\mathrm{Bern}(e^{-x/y}z/t)$ | Exact exp(-x/y)*z/t, x,z>=0,y,t>0, on its valid probability domain | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L121) | [**verified**](SampLib/Samplers/ExponentialRationalProduct.lean) |
| `Occil.Constants.inverseEPlus` | $\mathrm{Bern}((e+c-2)^{-1})$ | Exact 1/(e+c-2), for integer c>=1 | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L53) | — |
| `Occil.Constants.inverseEPlusContinuedFraction` | $\mathrm{Bern}((e+c-2)^{-1})$ | Exact rational-bound or series coin | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L86) | — |
| `Occil.Constants.inverseEPlusRational` | $\mathrm{Bern}((e+c-2)^{-1})$ | Exact 1/(e+c-2) for rational c=numerator/denominator>=1 | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L64) | [**verified**](SampLib/Samplers/InverseEPlusRational.lean) |
| `Occil.Constants.tanhHalf` | $\mathrm{Bern}\!\left(\tanh(1/2)\right)$ | Exact tanh(1/2)=(e-1)/(e+1) | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L93) | — |
| `Occil.Constants.threeMinusE` | $\mathrm{Bern}\!\left(3-e\right)$ | Exact rational-bound or series coin | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L46) | — |
## Constant coins / Numerical

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.numericalEulerReciprocal` | $\mathsf{Grid}_s[\text{numerical Euler Reciprocal}]$ | Finite-grid version of the fractional reciprocal identity for Euler's constant | [Numerical.lean](code/Samplers/Constants/Numerical.lean#L35) | — |
| `Occil.Constants.numericalExpRationalProduct` | $\mathsf{Grid}_s[\text{numerical Exp Rational Product}]$ | Exact rational-bound or series coin | [Numerical.lean](code/Samplers/Constants/Numerical.lean#L41) | — |
| `Occil.Constants.numericalLogPiOverPi` | $\mathsf{Grid}_s[\text{numerical Log Pi Over Pi}]$ | Exact rational-bound or series coin | [Numerical.lean](code/Samplers/Constants/Numerical.lean#L48) | — |
| `Occil.Constants.numericalLowerGammaRatio` | $\mathsf{Grid}_s[\text{numerical Lower Gamma Ratio}]$ | Exact rational-bound or series coin | [Numerical.lean](code/Samplers/Constants/Numerical.lean#L23) | — |
| `Occil.Constants.numericalRationalPower` | $\mathsf{Grid}_s[\text{numerical Rational Power}]$ | Exact rational-bound or series coin | [Numerical.lean](code/Samplers/Constants/Numerical.lean#L15) | — |
## Constant coins / Pi

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.arctanRationalOverRatio` | $\mathrm{Bern}(\arctan(x/y)/(x/y))$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L94) | — |
| `Occil.Constants.fourOverThreePi` | $\mathrm{Bern}\!\left(4/(3\pi)\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L82) | — |
| `Occil.Constants.inversePi` | $\mathrm{Bern}\!\left(1/\pi\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L80) | — |
| `Occil.Constants.inverseSqrtPi` | $\mathrm{Bern}\!\left(1/\sqrt\pi\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L91) | — |
| `Occil.Constants.logPiOverPi` | $\mathrm{Bern}\!\left(\log\pi/\pi\right)$ | Exact ln(pi)/pi by the geometric reciprocal-pi construction | [Pi.lean](code/Samplers/Constants/Pi.lean#L85) | — |
| `Occil.Constants.piAffine` | $\mathrm{Bern}((\pi-a)/b)$ | Bernoulli((pi-offset)/divisor); parameters must put the result in [0,1] | [Pi.lean](code/Samplers/Constants/Pi.lean#L49) | [**verified**](SampLib/Samplers/PiAffine.lean) |
| `Occil.Constants.piMinusThree` | $\mathrm{Bern}\!\left(\pi-3\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L66) | — |
| `Occil.Constants.piMinusThreeOverFour` | $\mathrm{Bern}\!\left((\pi-3)/4\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L64) | — |
| `Occil.Constants.piQuarter` | $\mathrm{Bern}\!\left(\pi/4\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L58) | — |
| `Occil.Constants.piQuarterMinusHalf` | $\mathrm{Bern}\!\left(\pi/4-1/2\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L62) | — |
| `Occil.Constants.piTwelfth` | $\mathrm{Bern}\!\left(\pi/12\right)$ | Exact rational-bound or series coin | [Pi.lean](code/Samplers/Constants/Pi.lean#L60) | — |
| `Occil.Constants.reciprocalPiScaled` | $\mathrm{Bern}\!\left(a/(b\pi)\right)$ | Bernoulli(numerator/(denominator*pi)), on its valid probability domain | [Pi.lean](code/Samplers/Constants/Pi.lean#L69) | [**verified**](SampLib/Samplers/ReciprocalPiScaled.lean) |
## Constant coins / Special

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.eOverPi` | $\mathrm{Bern}\!\left(e/\pi\right)$ | Exact e/pi from independently calculated rational interval bounds | [Special.lean](code/Samplers/Constants/Special.lean#L61) | [**verified**](SampLib/Samplers/EOverPi.lean) |
| `Occil.Constants.erfRatio` | $\mathrm{Bern}(\mathrm{erf}(x)/\mathrm{erf}(1))$ | Exact erf(x)/erf(1), 0<=x<=1 | [Special.lean](code/Samplers/Constants/Special.lean#L76) | — |
| `Occil.Constants.eulerMascheroni` | $\mathrm{Bern}\!\left(\gamma\right)$ | Exact rational-bound or series coin | [Special.lean](code/Samplers/Constants/Special.lean#L39) | — |
| `Occil.Constants.logOnePlusRational` | $\mathrm{Bern}\!\left(\log(1+x/y)\right)$ | Exact ln(1+x/y), 0<=x<=y | [Special.lean](code/Samplers/Constants/Special.lean#L49) | — |
| `Occil.Constants.lowerGammaIntegerRatio` | $\mathrm{Bern}(\gamma(m,x)/\gamma(m,1))$ | Exact gamma(m,x)/gamma(m,1) for integer m>0, x in [0,1] | [Special.lean](code/Samplers/Constants/Special.lean#L88) | — |
| `Occil.Constants.rationalIntegerPower` | $\mathrm{Bern}\!\left((a/b)^n\right)$ | Exact (a/b)^n for a rational base in [0,1] and integer n>=0 | [Special.lean](code/Samplers/Constants/Special.lean#L53) | — |
| `Occil.Constants.threeZetaThreeOverFour` | $\mathrm{Bern}\!\left(3\zeta(3)/4\right)$ | Exact 3*zeta(3)/4 | [Special.lean](code/Samplers/Constants/Special.lean#L18) | [**verified**](SampLib/Samplers/ThreeZetaThreeOverFour.lean) |
| `Occil.Constants.zetaRelated` | $\mathrm{Bern}\!\left(\zeta(k)(1-2^{1-k})\right)$ | Exact ζ(k)*(1-2^(1-k)), k>=2, by the k-fold geometric-bag integral | [Special.lean](code/Samplers/Constants/Special.lean#L25) | — |
## Continuous distributions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.erlang` | $\mathrm{Gamma}(k,1)$ | Sum independent unit exponentials | [Continuous.lean](code/Samplers/Continuous.lean#L33) | [**verified**](SampLib/Samplers/Erlang.lean) |
| `Occil.expHalfCoin` | $\mathrm{Bern}\!\left(e^{-1/2}\right)$ | Decreasing-chain parity below one half | [Continuous.lean](code/Samplers/Continuous.lean#L64) | [**verified**](SampLib/Samplers/ExpHalfCoin.lean) |
| `Occil.exponential` | $\mathrm{Exp}(1)$ | Von Neumann decreasing-chain parity | [Continuous.lean](code/Samplers/Continuous.lean#L20) | [**verified**](SampLib/Samplers/Exponential.lean) |
| `Occil.gaussian` | $\mathcal N(0,1)$ | Karney integer/fractional decomposition | [Continuous.lean](code/Samplers/Continuous.lean#L100) | [**verified**](SampLib/Samplers/Gaussian.lean) |
| `Occil.gaussianInteger` | $\Pr(K=k)\propto e^{-k^2/2},\ k\in\mathbb N$ | Reject geometric integer proposals | [Continuous.lean](code/Samplers/Continuous.lean#L95) | [**verified**](SampLib/Samplers/GaussianInteger.lean) |
| `Occil.geometricFailures` | $z+\mathrm{Geom}_0(1-p)$ | Count consecutive successes before failure | [Continuous.lean](code/Samplers/Continuous.lean#L75) | [**verified**](SampLib/Samplers/GeometricFailures.lean) |
| `Occil.iterateCoin` | $\mathrm{Bern}\!\left(p^n\right)$ | Require all independent trials to succeed | [Continuous.lean](code/Samplers/Continuous.lean#L71) | [**verified**](SampLib/Samplers/IterateCoin.lean) |
| `Occil.laplace` | $\mathrm{Laplace}(0,1)$ | Exponential magnitude and fair sign | [Continuous.lean](code/Samplers/Continuous.lean#L29) | [**verified**](SampLib/Samplers/Laplace.lean) |
| `Occil.mixture` | $p\mu+(1-p)\nu$ | A mixture of two abstract samplers selected by a coin callback | [Continuous.lean](code/Samplers/Continuous.lean#L58) | [**verified**](SampLib/Samplers/Mixture.lean) |
| `Occil.orderStatistic` | $U_{(k:n)}$ | Return kth of n sorted independent unit uniforms | [Continuous.lean](code/Samplers/Continuous.lean#L49) | [**verified**](SampLib/Samplers/OrderStatistic.lean) |
| `Occil.uniformMax` | $\mathrm{Beta}(2,1)$ | Maximum of two uniform draws | [Continuous.lean](code/Samplers/Continuous.lean#L45) | [**verified**](SampLib/Samplers/UniformMax.lean) |
| `Occil.uniformMin` | $\mathrm{Beta}(1,2)$ | Minimum of two uniform draws | [Continuous.lean](code/Samplers/Continuous.lean#L42) | [**verified**](SampLib/Samplers/UniformMin.lean) |
| `Occil.uniformSum` | $\sum_{i=1}^n U_i,\ U_i\sim\mathrm{Unif}(0,1)$ | Sum independent continuous uniforms | [Continuous.lean](code/Samplers/Continuous.lean#L37) | [**verified**](SampLib/Samplers/UniformSum.lean) |
## Discrete distributions / Binomial

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.binomialBinary` | $\mathrm{Bin}(n,a/b)$ | Farach-Colton–Tsai binary expansion of the rational success probability | [Binomial.lean](code/Samplers/Discrete/Binomial.lean#L49) | [**verified**](SampLib/Samplers/BinomialBinary.lean) |
| `Occil.DiscreteExtra.binomialHalfBits` | $\mathrm{Bin}(n,1/2)$ | One uniform integer supplies n fair bits; count its set bits | [Binomial.lean](code/Samplers/Discrete/Binomial.lean#L19) | [**verified**](SampLib/Samplers/BinomialHalfBits.lean) |
| `Occil.DiscreteExtra.binomialHalfRejection` | $\mathrm{Bin}(n,1/2)$ | Bringmann's exact envelope-rejection algorithm for Binomial(n,1/2) | [Binomial.lean](code/Samplers/Discrete/Binomial.lean#L29) | — |
## Discrete distributions / Bounded

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.boundedGeometric` | $\min(\mathrm{Geom}_0(p),n)$ | Bounded failures before success (the direct trial variant) | [Bounded.lean](code/Samplers/Discrete/Bounded.lean#L12) | [**verified**](SampLib/Samplers/BoundedGeometric.lean) |
## Discrete distributions / Compound

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.compoundPoisson` | $\sum_{i=1}^{N}X_i,\ N\sim\mathrm{Pois}(\lambda)$ | Sum a Poisson number of independent integer-valued jumps | [Compound.lean](code/Samplers/Discrete/Compound.lean#L19) | [**verified**](SampLib/Samplers/CompoundPoisson.lean) |
| `Occil.DiscreteExtra.cub` | $\pi(1+\mathrm{Bin}(m-1,1-p))+(1-\pi)\mathrm{Unif}\{1,\ldots,m\}$ | CUB/MUB: mixture of a shifted binomial and a discrete uniform on 1..m | [Compound.lean](code/Samplers/Discrete/Compound.lean#L75) | [**verified**](SampLib/Samplers/Cub.lean) |
| `Occil.DiscreteExtra.multivariatePoisson` | $(Z_0+Z_i)_i,\ Z_i\text{ independent Poisson}$ | Shared-component multivariate Poisson | [Compound.lean](code/Samplers/Discrete/Compound.lean#L49) | [**verified**](SampLib/Samplers/MultivariatePoisson.lean) |
| `Occil.DiscreteExtra.negativeMultinomial` | $\mathrm{NegMultinomial}(r,w)$ | Counts of each failure category before r successes | [Compound.lean](code/Samplers/Discrete/Compound.lean#L60) | [**verified**](SampLib/Samplers/NegativeMultinomial.lean) |
| `Occil.DiscreteExtra.neymanTypeA` | $\mathrm{NeymanA}(\lambda,\mu)$ | Neyman type A: Poisson(delta) independent Poisson(tau) clusters | [Compound.lean](code/Samplers/Discrete/Compound.lean#L43) | [**verified**](SampLib/Samplers/NeymanTypeA.lean) |
| `Occil.DiscreteExtra.polyaAeppli` | $\mathrm{PolyaAeppli}(\lambda,p)$ | Compound Poisson with geometric jumps on 1,2, | [Compound.lean](code/Samplers/Discrete/Compound.lean#L35) | [**verified**](SampLib/Samplers/PolyaAeppli.lean) |
| `Occil.DiscreteExtra.skellam` | $\mathrm{Pois}(\lambda_1)-\mathrm{Pois}(\lambda_2)$ | Difference of two independent Poisson random variables | [Compound.lean](code/Samplers/Discrete/Compound.lean#L27) | [**verified**](SampLib/Samplers/Skellam.lean) |
## Discrete distributions / Counts

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.betaNegativeBinomial` | $\mathrm{BetaNegBin}(r,\alpha,\beta)$ | Beta-negative-binomial mixture with positive rational beta shapes | [Counts.lean](code/Samplers/Discrete/Counts.lean#L48) | — |
| `Occil.DiscreteExtra.borel` | $\mathrm{Borel}(\lambda)$ | Borel(lambda): total progeny of a Poisson branching process | [Counts.lean](code/Samplers/Discrete/Counts.lean#L68) | [**verified**](SampLib/Samplers/Borel.lean) |
| `Occil.DiscreteExtra.inversePolya` | $\mathrm{InversePolya}(r,a,b,c)$ | Failures before a prescribed number of successes in a reinforced urn | [Counts.lean](code/Samplers/Discrete/Counts.lean#L39) | — |
| `Occil.DiscreteExtra.logarithmicSeries` | $\Pr(N=k)=-\frac{p^k}{k\log(1-p)}$ | Logarithmic-series(p), 0 < p < 1, by geometric proposals and 1/n rejection | [Counts.lean](code/Samplers/Discrete/Counts.lean#L78) | [**verified**](SampLib/Samplers/LogarithmicSeries.lean) |
| `Occil.DiscreteExtra.polyaRational` | $\mathrm{NegBin}(r,p)$ | Exact integer-valued construction | [Counts.lean](code/Samplers/Discrete/Counts.lean#L21) | — |
| `Occil.DiscreteExtra.waringYule` | $\mathrm{BetaNegBin}(1,\alpha,\beta)$ | Waring–Yule: one success in a beta-mixed geometric distribution | [Counts.lean](code/Samplers/Discrete/Counts.lean#L57) | — |
| `Occil.DiscreteExtra.yuleSimon` | $\mathrm{YuleSimon}(\rho)$ | Yule–Simon(rho), supported on positive integers; rho is a positive rational | [Counts.lean](code/Samplers/Discrete/Counts.lean#L62) | — |
| `Occil.DiscreteExtra.zeroTruncatedPoisson` | $\mathrm{Pois}(\lambda)\mid N>0$ | Poisson conditioned to be strictly positive | [Counts.lean](code/Samplers/Discrete/Counts.lean#L88) | [**verified**](SampLib/Samplers/ZeroTruncatedPoisson.lean) |
## Discrete distributions / Numerical

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.bell` | $\mathsf{Grid}_s[\mathrm{bell}]$ | The standard one-parameter Bell distribution: Bell–Touchard(a,1) | [Numerical.lean](code/Samplers/Discrete/Numerical.lean#L50) | — |
| `Occil.DiscreteExtra.bellTouchard` | $\mathsf{Grid}_s[\text{bell Touchard}]$ | Bell–Touchard(a,b): sum Poisson(b*(exp(a)-1)) positive Poisson(a) clusters | [Numerical.lean](code/Samplers/Discrete/Numerical.lean#L41) | — |
| `Occil.DiscreteExtra.betaNegativeBinomialNumerical` | $\mathsf{Grid}_s[\text{beta Negative Binomial Numerical}]$ | Beta-negative-binomial with arbitrary numerical beta shapes and an integer success count | [Numerical.lean](code/Samplers/Discrete/Numerical.lean#L31) | — |
| `Occil.DiscreteExtra.discretePareto` | $\mathsf{Grid}_s[\text{discrete Pareto}]$ | Discrete Pareto(delta,p), supported on 1,2,..., by the gamma mixture in randmisc.html | [Numerical.lean](code/Samplers/Discrete/Numerical.lean#L55) | — |
| `Occil.DiscreteExtra.negativeBinomialNumerical` | $\mathsf{Grid}_s[\text{negative Binomial Numerical}]$ | Exact integer-valued construction | [Numerical.lean](code/Samplers/Discrete/Numerical.lean#L19) | — |
## Discrete distributions / Tails

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.discreteLaplace` | $\Pr(K=k)\propto e^{-\epsilon\lvert k\rvert}$ | Canonne et al | [Tails.lean](code/Samplers/Discrete/Tails.lean#L38) | [**verified**](SampLib/Samplers/DiscreteLaplace.lean) |
| `Occil.DiscreteExtra.generalizedGeometric` | $\Pr(K=k)=(1-\rho_k)\prod_{j<k}\rho_j$ | Generalized geometric: rho(k) returns a continuation coin at positive k | [Tails.lean](code/Samplers/Discrete/Tails.lean#L96) | — |
| `Occil.DiscreteExtra.generalizedSibuya` | $\Pr(K=k)=\frac{\alpha}{\nu+k}\prod_{j<k}\left(1-\frac\alpha{\nu+j}\right)$ | Generalized Sibuya with alpha>0, nu>=0 and alpha<nu+1, all rational | [Tails.lean](code/Samplers/Discrete/Tails.lean#L102) | — |
| `Occil.DiscreteExtra.himanshu` | $\mathrm{Geom}_0(p^m)$ | Himanshu: failures before n consecutive coin successes in independent blocks | [Tails.lean](code/Samplers/Discrete/Tails.lean#L115) | [**verified**](SampLib/Samplers/Himanshu.lean) |
| `Occil.DiscreteExtra.logUniform` | $\text{uniform logarithmic bucket, then uniform integer}$ | Abseil-style log-uniform integers in [0,maximum], integer base>=2 | [Tails.lean](code/Samplers/Discrete/Tails.lean#L53) | [**verified**](SampLib/Samplers/LogUniform.lean) |
| `Occil.DiscreteExtra.rationalPowerCoin` | $\mathrm{Bern}(p^{a/b})$ | Extend the power factory to any nonnegative rational exponent | [Tails.lean](code/Samplers/Discrete/Tails.lean#L21) | — |
| `Occil.DiscreteExtra.symmetricGeometric` | $\Pr(K=k)\propto(1-p)^{\lvert k\rvert}$ | Symmetric geometric with tails proportional to (1-p)^&#124;k&#124; | [Tails.lean](code/Samplers/Discrete/Tails.lean#L32) | [**verified**](SampLib/Samplers/SymmetricGeometric.lean) |
| `Occil.DiscreteExtra.zeta` | $\Pr(K=k)=k^{-s}/\zeta(s)$ | Zeta(alpha), alpha>1 rational | [Tails.lean](code/Samplers/Discrete/Tails.lean#L80) | — |
| `Occil.DiscreteExtra.zipf` | $\Pr(K=k)\propto k^{-s},\ 1\le k\le n$ | Zipf on 1..bound, with any nonnegative rational exponent | [Tails.lean](code/Samplers/Discrete/Tails.lean#L68) | — |
## Discrete distributions / Urns

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.betaBinomial` | $\mathrm{BetaBin}(n,\alpha,\beta)$ | Beta-binomial with positive rational beta shapes, using a reinforced urn | [Urns.lean](code/Samplers/Discrete/Urns.lean#L51) | [**verified**](SampLib/Samplers/BetaBinomial.lean) |
| `Occil.DiscreteExtra.fisherHypergeometric` | $\Pr(K=k)\propto\binom ak\binom b{n-k}\omega^k$ | Fisher noncentral hypergeometric, by its exact finite integer-weight table | [Urns.lean](code/Samplers/Discrete/Urns.lean#L30) | [**verified**](SampLib/Samplers/FisherHypergeometric.lean) |
| `Occil.DiscreteExtra.fisherMultivariate` | $\Pr(K=k)\propto\prod_i\binom{c_i}{k_i}w_i^{k_i},\ \sum_i k_i=n$ | Multicolor Fisher noncentral hypergeometric by independent binomials conditioned on their total | [Urns.lean](code/Samplers/Discrete/Urns.lean#L103) | [**verified**](SampLib/Samplers/FisherMultivariate.lean) |
| `Occil.DiscreteExtra.multivariateHypergeometric` | $\Pr(K=k)=\frac{\prod_i\binom{c_i}{k_i}}{\binom{\sum_i c_i}n}$ | Multivariate hypergeometric is the equal-odds multicolor urn | [Urns.lean](code/Samplers/Discrete/Urns.lean#L95) | [**verified**](SampLib/Samplers/MultivariateHypergeometric.lean) |
| `Occil.DiscreteExtra.negativeHypergeometric` | $\mathrm{NegHypergeom}(a,b,r)$ | Negative hypergeometric: failures before r successes without replacement | [Urns.lean](code/Samplers/Discrete/Urns.lean#L42) | [**verified**](SampLib/Samplers/NegativeHypergeometric.lean) |
| `Occil.DiscreteExtra.walleniusHypergeometric` | $\mathrm{WalleniusHypergeom}(a,b,n,\omega)$ | Wallenius noncentral hypergeometric, by weighted sampling without replacement | [Urns.lean](code/Samplers/Discrete/Urns.lean#L19) | [**verified**](SampLib/Samplers/WalleniusHypergeometric.lean) |
| `Occil.DiscreteExtra.walleniusMultivariate` | $\mathrm{WalleniusMultivariate}(n,c,w)$ | Multicolor Wallenius urn with positive integer odds, returned as color counts | [Urns.lean](code/Samplers/Discrete/Urns.lean#L82) | [**verified**](SampLib/Samplers/WalleniusMultivariate.lean) |
## Discrete primitives

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.binomial` | $\mathrm{Bin}(n,p)$ | Count independent successful trials | [Discrete.lean](code/Samplers/Discrete.lean#L12) | [**verified**](SampLib/Samplers/Binomial.lean) |
| `Occil.dice` | $\sum_{i=1}^n\mathrm{Unif}_i\{1,\ldots,s\}$ | Sum independent uniform dice | [Discrete.lean](code/Samplers/Discrete.lean#L28) | [**verified**](SampLib/Samplers/Dice.lean) |
| `Occil.geometric` | $\mathrm{Geom}_0(p)$ | Count failures before success | [Discrete.lean](code/Samplers/Discrete.lean#L20) | [**verified**](SampLib/Samplers/Geometric.lean) |
| `Occil.hypergeometric` | $\mathrm{Hypergeom}(a+b,a,n)$ | Deplete selected urn color | [Discrete.lean](code/Samplers/Discrete.lean#L79) | [**verified**](SampLib/Samplers/Hypergeometric.lean) |
| `Occil.multinomial` | $\mathrm{Multinomial}(n,w/\sum_iw_i)$ | Sequential conditional binomial counts | [Discrete.lean](code/Samplers/Discrete.lean#L54) | [**verified**](SampLib/Samplers/Multinomial.lean) |
| `Occil.negativeBinomial` | $\sum_{i=1}^r\mathrm{Geom}_{0,i}(p)$ | Sum independent geometric counts | [Discrete.lean](code/Samplers/Discrete.lean#L23) | [**verified**](SampLib/Samplers/NegativeBinomial.lean) |
| `Occil.poissonOne` | $\mathrm{Pois}(1)$ | Duchon–Duvignau integer state machine | [Discrete.lean](code/Samplers/Discrete.lean#L95) | [**verified**](SampLib/Samplers/PoissonOne.lean) |
| `Occil.poissonRational` | $\mathrm{Pois}(x/y)$ | Poisson additivity and binomial thinning | [Discrete.lean](code/Samplers/Discrete.lean#L106) | [**verified**](SampLib/Samplers/PoissonRational.lean) |
| `Occil.polyaEggenberger` | $\mathrm{PolyaUrn}(n,a,b,c)$ | Reinforce selected urn color | [Discrete.lean](code/Samplers/Discrete.lean#L70) | [**verified**](SampLib/Samplers/PolyaEggenberger.lean) |
| `Occil.randomWalk` | $\sum_{i=1}^n\mathrm{Unif}_i\{-1,1\}$ | Sum independent fair signs | [Discrete.lean](code/Samplers/Discrete.lean#L88) | [**verified**](SampLib/Samplers/RandomWalk.lean) |
| `Occil.weightedChoice` | $\mathrm{Cat}(w)$ | Cumulative integer weight intervals | [Discrete.lean](code/Samplers/Discrete.lean#L33) | [**verified**](SampLib/Samplers/WeightedChoice.lean) |
## General sampling / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.couplingFromPast` | $\pi,\quad\pi K=\pi$ | Propp–Wilson doubling of shared maps | [Core.lean](code/Samplers/General/Core.lean#L237) | [**verified**](SampLib/Samplers/CouplingFromPast.lean) |
| `Occil.General.discreteCDF` | $\Pr(K=i)=(C_i-C_{i-1})/C_{n-1}$ | Binary-search cumulative integer masses | [Core.lean](code/Samplers/General/Core.lean#L56) | [**verified**](SampLib/Samplers/DiscreteCDF.lean) |
| `Occil.General.episodes` | $(\sum_{i=1}^{N}X_i,N)$ | Return stopped sum with sampled count | [Core.lean](code/Samplers/General/Core.lean#L392) | [**verified**](SampLib/Samplers/Episodes.lean) |
| `Occil.General.gibbsSweep` | $(K_1\cdots K_d)(x,\cdot)$ | Sequential conditional coordinate updates | [Core.lean](code/Samplers/General/Core.lean#L279) | [**verified**](SampLib/Samplers/GibbsSweep.lean) |
| `Occil.General.incompleteInformation` | $\mathrm{Cat}(p)$ | Finite inverse-CDF sampling when only improving probability bounds are known | [Core.lean](code/Samplers/General/Core.lean#L188) | — |
| `Occil.General.inverseCDF` | $\Pr(X\le x)=C(x)/s$ | Binary-search a sampled CDF rank | [Core.lean](code/Samplers/General/Core.lean#L72) | [**verified**](SampLib/Samplers/InverseCDF.lean) |
| `Occil.General.inverseQuantile` | $Q_*\mathrm{Unif}\{1,\ldots,s-1\}$ | Transform a uniform grid rank | [Core.lean](code/Samplers/General/Core.lean#L49) | [**verified**](SampLib/Samplers/InverseQuantile.lean) |
| `Occil.General.markovChain` | $K^n(x,\cdot)$ | Iterate row-normalized transition kernel | [Core.lean](code/Samplers/General/Core.lean#L207) | [**verified**](SampLib/Samplers/MarkovChain.lean) |
| `Occil.General.markovStep` | $K(x,\cdot)$ | A transition matrix is a list of nonnegative integer weight rows | [Core.lean](code/Samplers/General/Core.lean#L203) | [draft](SampLib/Samplers/MarkovChain.lean) |
| `Occil.General.markovTrajectory` | $\prod_{t=1}^n K(x_{t-1},dx_t)$ | Record each transition destination | [Core.lean](code/Samplers/General/Core.lean#L213) | [**verified**](SampLib/Samplers/MarkovTrajectory.lean) |
| `Occil.General.metropolis` | $K_{\mathrm{Metropolis}}^n(x,\cdot)$ | Symmetric-proposal acceptance step | [Core.lean](code/Samplers/General/Core.lean#L273) | [**verified**](SampLib/Samplers/CountableMetropolis.lean) |
| `Occil.General.metropolisHastings` | $K_{\mathrm{MH}}^n(x,\cdot)$ | Proposal followed by Hastings acceptance | [Core.lean](code/Samplers/General/Core.lean#L258) | [**verified**](SampLib/Samplers/CountableMetropolisHastings.lean) |
| `Occil.General.pdfRejection` | $\Pr(X=x)\propto h(x),\ x\in\{\ell,\ldots,u-1\}$ | Uniform grid proposal and height test | [Core.lean](code/Samplers/General/Core.lean#L85) | [**verified**](SampLib/Samplers/PdfRejection.lean) |
| `Occil.General.perfectFiniteChain` | $\pi,\quad\pi K=\pi$ | Shared random-map CFTP construction | [Core.lean](code/Samplers/General/Core.lean#L250) | [**verified**](SampLib/Samplers/PerfectFiniteChain.lean) |
| `Occil.General.permutationTest` | $\frac{1+\#\{i:T(\Pi_i x)\ge T(x)\}}{B+1}$ | A Monte Carlo permutation-test p-value as an exact (numerator,denominator) pair | [Core.lean](code/Samplers/General/Core.lean#L344) | [**verified**](SampLib/Samplers/PermutationTest.lean) |
| `Occil.General.piecewiseConstant` | $\Pr(X=x)\propto h_i,\ a_i\le x<a_{i+1}$ | Choose bin by area, then uniform | [Core.lean](code/Samplers/General/Core.lean#L102) | [**verified**](SampLib/Samplers/PiecewiseConstant.lean) |
| `Occil.General.piecewiseLinear` | $\Pr(X=x)\propto h_i+\frac{x-a_i}{a_{i+1}-a_i}(h_{i+1}-h_i)$ | Select bin, then reject by height | [Core.lean](code/Samplers/General/Core.lean#L123) | [**verified**](SampLib/Samplers/PiecewiseLinear.lean) |
| `Occil.General.randomDateTime` | $\mathrm{Unif}\{\ell,\ldots,h\}$ | Uniform integral timestamp in an inclusive application-specified epoch range | [Core.lean](code/Samplers/General/Core.lean#L42) | [**verified**](SampLib/Samplers/RandomDateTime.lean) |
| `Occil.General.randomMap` | $\bigotimes_i K(i,\cdot)$ | Independent destination per source state | [Core.lean](code/Samplers/General/Core.lean#L221) | [**verified**](SampLib/Samplers/RandomMap.lean) |
| `Occil.General.randomScanGibbs` | $\left(d^{-1}\sum_i K_i\right)^n(x,\cdot)$ | Uniformly select conditional coordinate updates | [Core.lean](code/Samplers/General/Core.lean#L287) | [**verified**](SampLib/Samplers/RandomScanGibbs.lean) |
| `Occil.General.randomString` | $\mathrm{Unif}(\text{alphabet})^{\otimes n}$ | Uniform character/item sequences; output is a list, not a host string | [Core.lean](code/Samplers/General/Core.lean#L38) | [**verified**](SampLib/Samplers/RandomString.lean) |
| `Occil.General.randomWalkPath` | $(x,x+X_1,\ldots,x+\sum_{i=1}^n X_i)$ | Accumulate and record independent increments | [Core.lean](code/Samplers/General/Core.lean#L357) | [**verified**](SampLib/Samplers/RandomWalkPath.lean) |
| `Occil.General.refinedCDFComparison` | $\mathrm{Bern}(F(x))$ | Compare a shared U with a cumulative-probability oracle | [Core.lean](code/Samplers/General/Core.lean#L173) | — |
| `Occil.General.refinedCoin` | $\mathrm{Bern}(p)$ | A bounds callback returns numerators (lower,upper) at denominator 2^level | [Core.lean](code/Samplers/General/Core.lean#L157) | — |
| `Occil.General.shapeRejection` | $\mu(\cdot\mid A)$ | Rejection in any bounded shape | [Core.lean](code/Samplers/General/Core.lean#L97) | — |
| `Occil.General.sliceSampler` | $K_{\mathrm{slice}}^n(x,\cdot)$ | Iterate bounded slice transitions | [Core.lean](code/Samplers/General/Core.lean#L303) | [**verified**](SampLib/Samplers/SliceSampler.lean) |
| `Occil.General.sliceSamplerStepOut` | $K_{\mathrm{stepout}}^n(x,\cdot)$ | Iterate stepping-out slice transitions | [Core.lean](code/Samplers/General/Core.lean#L336) | — |
| `Occil.General.sliceStepOut` | $K_{\mathrm{stepout}}(x,\cdot)$ | Step out, then shrink slice bracket | [Core.lean](code/Samplers/General/Core.lean#L312) | — |
| `Occil.General.stoppedMaximum` | $\max_{1\le i\le N}X_i$ | Maximum over a random count | [Core.lean](code/Samplers/General/Core.lean#L382) | [**verified**](SampLib/Samplers/StoppedMaximum.lean) |
| `Occil.General.stoppedMinimum` | $\min_{1\le i\le N}X_i$ | Minimum over a random count | [Core.lean](code/Samplers/General/Core.lean#L373) | [**verified**](SampLib/Samplers/StoppedMinimum.lean) |
| `Occil.General.stoppedSum` | $\sum_{i=1}^{N}X_i$ | Sum a randomly sampled count | [Core.lean](code/Samplers/General/Core.lean#L366) | [**verified**](SampLib/Samplers/StoppedSum.lean) |
## General sampling / DataModels

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.bootstrap` | $\left(\widehat\mu^{\otimes n}\right)^{\otimes B}$ | Independent empirical resampling data sets | [DataModels.lean](code/Samplers/General/DataModels.lean#L16) | [**verified**](SampLib/Samplers/Bootstrap.lean) |
| `Occil.General.classifiedModel` | $\sum_i\frac{w_i}{\sum_jw_j}(\delta_i\otimes\mu_i)$ | Choose class and conditional model | [DataModels.lean](code/Samplers/General/DataModels.lean#L117) | [**verified**](SampLib/Samplers/ClassifiedModel.lean) |
| `Occil.General.gaussianKernelDensity` | $\mathsf{Grid}_s[\widehat\mu*\mathcal N(0,h^2)]$ | Empirical center plus Gaussian jitter | [DataModels.lean](code/Samplers/General/DataModels.lean#L86) | — |
| `Occil.General.gaussianKernelDensityVector` | $\mathsf{Grid}_s[\widehat\mu*\mathcal N(0,h^2I)]$ | Empirical vector plus coordinatewise Gaussian jitter | [DataModels.lean](code/Samplers/General/DataModels.lean#L90) | — |
| `Occil.General.gaussianMixture` | $\mathsf{Grid}_s[\sum_iw_i\mathcal N(\mu_i,\sigma_i^2)/\sum_iw_i]$ | Weighted Gaussian component selection | [DataModels.lean](code/Samplers/General/DataModels.lean#L64) | — |
| `Occil.General.generativeModel` | $g_*\mu$ | Decode an independent latent sample | [DataModels.lean](code/Samplers/General/DataModels.lean#L110) | [**verified**](SampLib/Samplers/GenerativeModel.lean) |
| `Occil.General.groupedPermutation` | $\mathrm{Unif}(\text{fixed-size position partitions})$ | Shuffle and split at fixed sizes | [DataModels.lean](code/Samplers/General/DataModels.lean#L38) | [**verified**](SampLib/Samplers/GroupedPermutation.lean) |
| `Occil.General.histogram` | $\Pr(X=x)=\frac{c_i}{(a_{i+1}-a_i)\sum_jc_j},\ a_i\le x<a_{i+1}$ | Choose bin by mass, then uniform | [DataModels.lean](code/Samplers/General/DataModels.lean#L53) | [**verified**](SampLib/Samplers/Histogram.lean) |
| `Occil.General.kernelDensity` | $\widehat\mu*\kappa$ | Empirical center plus independent jitter | [DataModels.lean](code/Samplers/General/DataModels.lean#L74) | [**verified**](SampLib/Samplers/KernelDensity.lean) |
| `Occil.General.kernelDensityVector` | $\widehat\mu*\kappa^{\otimes d}$ | Shared empirical center, coordinatewise jitter | [DataModels.lean](code/Samplers/General/DataModels.lean#L81) | [**verified**](SampLib/Samplers/KernelDensityVector.lean) |
| `Occil.General.linearRegression` | $\mathsf{Grid}_s[\mathcal N(\beta_0+\beta^\top x,\mathrm{MSE})]$ | Linear predictor plus Gaussian residual | [DataModels.lean](code/Samplers/General/DataModels.lean#L97) | — |
| `Occil.General.permutationSamples` | $\mathrm{Unif}(S_n)^{\otimes B}$ | Repeat independent uniform shuffles | [DataModels.lean](code/Samplers/General/DataModels.lean#L23) | [**verified**](SampLib/Samplers/PermutationSamples.lean) |
| `Occil.General.stochasticInterpolation` | $\mathsf{Grid}_s[\text{nearest-neighbor interpolation}]$ | Nearest-neighbor vectors with shared random weights | [DataModels.lean](code/Samplers/General/DataModels.lean#L174) | — |
## General sampling / Points

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.bestCandidate` | $\text{farthest of uniform candidate points}$ | Best-candidate point selection | [Points.lean](code/Samplers/General/Points.lean#L255) | — |
| `Occil.General.farthestPoints` | $\text{greedy farthest-candidate point set}$ | Greedy farthest-point traversal of a finite candidate pool | [Points.lean](code/Samplers/General/Points.lean#L275) | — |
| `Occil.General.latinHypercube` | $\text{independent shuffled stratifications by coordinate}$ | Independently shuffle coordinate stratifications | [Points.lean](code/Samplers/General/Points.lean#L160) | [**verified**](SampLib/Samplers/LatinHypercube.lean) |
| `Occil.General.latinHypercube1D` | $\text{uniform shuffle of stratified draws}$ | Shuffle one-dimensional stratified draws | [Points.lean](code/Samplers/General/Points.lean#L155) | [**verified**](SampLib/Samplers/LatinHypercube1D.lean) |
| `Occil.General.poissonDiskRejection` | $\text{sequential hard-core grid proposals}$ | Random sequential hard-core (Poisson-disk) rejection on a finite grid | [Points.lean](code/Samplers/General/Points.lean#L296) | — |
| `Occil.General.stratified1D` | $\bigotimes_i\mathrm{Unif}\{\lfloor is/n\rfloor,\ldots,\lfloor(i+1)s/n\rfloor-1\}$ | One uniform integer per stratum | [Points.lean](code/Samplers/General/Points.lean#L145) | [**verified**](SampLib/Samplers/Stratified1D.lean) |
| `Occil.General.stratifiedBox` | $\text{independent uniform draws per grid cell}$ | Jitter independently within Cartesian cells | [Points.lean](code/Samplers/General/Points.lean#L182) | [**verified**](SampLib/Samplers/StratifiedBox.lean) |
| `Occil.General.stratifiedCell` | $\mathrm{Unif}(\text{integer-grid cell})$ | One jittered point from the cell whose base-bins digits give its coordinate indices | [Points.lean](code/Samplers/General/Points.lean#L170) | [draft](SampLib/Samplers/StratifiedCell.lean) |
| `Occil.General.uniformBoxPoint` | $\mathrm{Unif}\{0,\ldots,s-1\}^{\otimes d}$ | Independent uniform integer coordinates | [Points.lean](code/Samplers/General/Points.lean#L226) | [**verified**](SampLib/Samplers/UniformBoxPoint.lean) |
## Integer and weighted sampling / Aliases

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.voseDraw` | $\mathrm{Cat}(w)$ | Integer-weight sampling construction (valid table required) | [Aliases.lean](code/Samplers/Weighted/Aliases.lean#L57) | — |
| `Occil.WeightedVariants.voseSamples` | $\mathrm{Cat}(w)^{\otimes k}$ | Integer-weight sampling construction | [Aliases.lean](code/Samplers/Weighted/Aliases.lean#L68) | [**verified**](SampLib/Samplers/VoseSamples.lean) |
## Integer and weighted sampling / Choice

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.flatChoice` | $\mathrm{Cat}(w)$ | Expand weights into a uniform table | [Choice.lean](code/Samplers/Weighted/Choice.lean#L56) | [**verified**](SampLib/Samplers/FlatChoice.lean) |
| `Occil.WeightedVariants.sequentialCoins` | $\mathrm{Cat}(w)$ | Sequential conditional rational coins | [Choice.lean](code/Samplers/Weighted/Choice.lean#L18) | [**verified**](SampLib/Samplers/SequentialCoins.lean) |
| `Occil.WeightedVariants.twoLevelChoice` | $\mathrm{Cat}(w)$ | Select block, then within-block category | [Choice.lean](code/Samplers/Weighted/Choice.lean#L31) | [**verified**](SampLib/Samplers/TwoLevelChoice.lean) |
## Integer and weighted sampling / Dynamic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.fenwickDraw` | $\mathrm{Cat}(w)$ | Invert cumulative mass by binary lifting through a mutable Fenwick tree (valid table required) | [Dynamic.lean](code/Samplers/Weighted/Dynamic.lean#L68) | [**verified**](SampLib/Samplers/FenwickDraw.lean) |
## Integer and weighted sampling / Optimal

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.optimalChoice` | $\mathrm{Cat}(w)$ | Integer-weight sampling construction | [Optimal.lean](code/Samplers/Weighted/Optimal.lean#L72) | — |
| `Occil.WeightedVariants.optimalDraw` | $\mathrm{Cat}(w)$ | Traverse a finite cyclic probability matrix directly, as nextFromMatrix (valid table required) | [Optimal.lean](code/Samplers/Weighted/Optimal.lean#L52) | — |
## Integer and weighted sampling / Reductions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.moduloReduction` | $(x\mapsto x\bmod n)_*\mathrm{Unif}\{0,\ldots,2^b-1\}$ | Approximate modulo reduction | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L16) | [**verified**](SampLib/Samplers/WordReductions.lean) |
| `Occil.Weighted.multiplyShift` | $(x\mapsto\lfloor nx/2^b\rfloor)_*\mathrm{Unif}\{0,\ldots,2^b-1\}$ | Approximate multiply-and-shift reduction, with an explicit input bit count | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L22) | [**verified**](SampLib/Samplers/WordReductions.lean) |
| `Occil.WeightedVariants.debiasedModulo` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Discard incomplete low residue interval | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L84) | [**verified**](SampLib/Samplers/DebiasedModulo.lean) |
| `Occil.WeightedVariants.divisionRejection` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Reject excess quotient buckets | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L73) | [**verified**](SampLib/Samplers/DivisionRejection.lean) |
| `Occil.WeightedVariants.floatingMultiply` | $\left(x\mapsto\lfloor\mathrm{round}_p(nx)/2^b\rfloor\right)_*\mathrm{Unif}\{0,\ldots,2^b-1\}$ | O'Neill's biased floating-point multiply, emulated with integer arithmetic | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L66) | [**verified**](SampLib/Samplers/FloatingMultiply.lean) |
| `Occil.WeightedVariants.lemireUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Reject multiply-high low-word bias | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L38) | [**verified**](SampLib/Samplers/LemireUniform.lean) |
| `Occil.WeightedVariants.oneillUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Lazy-threshold multiply-high rejection | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L96) | [**verified**](SampLib/Samplers/OneillUniform.lean) |
## Integer and weighted sampling / Rejection

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.sortedChoice` | $\mathrm{Cat}(w)$ | Integer-weight sampling construction | [Rejection.lean](code/Samplers/Weighted/Rejection.lean#L17) | — |
| `Occil.WeightedVariants.succinctChoice` | $\mathrm{Cat}(w)$ | Bringmann–Larsen's packed 20/32-bit weights | [Rejection.lean](code/Samplers/Weighted/Rejection.lean#L53) | — |
## Integer and weighted sampling / Reservoir

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.inclusionSplitting` | $\#S=k,\quad\Pr(i\in S)=kw_i/\sum_jw_j\ \text{(marginals)}$ | Deville–Tillé splitting with prescribed inclusion marginals | [Reservoir.lean](code/Samplers/Weighted/Reservoir.lean#L44) | — |
| `Occil.Weighted.inclusionSystematic` | $\#S=k,\quad\Pr(i\in S)=kw_i/\sum_jw_j\ \text{(marginals)}$ | Shifted lattice with prescribed inclusion marginals | [Reservoir.lean](code/Samplers/Weighted/Reservoir.lean#L86) | — |
| `Occil.Weighted.weightedReservoirOne` | $\mathrm{Cat}(w)$ | Running-weight replacement decisions | [Reservoir.lean](code/Samplers/Weighted/Reservoir.lean#L17) | [**verified**](SampLib/Samplers/WeightedReservoirOne.lean) |
## Integer and weighted sampling / Sequential

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.aliasSamples` | $\mathrm{Cat}(w)^{\otimes k}$ | Walker alias preprocessing and repeated draws | [Sequential.lean](code/Samplers/Weighted/Sequential.lean#L42) | [**verified**](SampLib/Samplers/AliasSamples.lean) |
| `Occil.weightedRejection` | $\mathrm{Cat}(w)$ | Uniform category with envelope acceptance | [Sequential.lean](code/Samplers/Weighted/Sequential.lean#L12) | [**verified**](SampLib/Samplers/WeightedRejection.lean) |
| `Occil.weightedWithoutReplacement` | $\Pr(i_1,\ldots,i_k)=\prod_{j=1}^k\frac{w_{i_j}}{\sum_{i\notin\{i_1,\ldots,i_{j-1}\}}w_i}$ | Select weight, then zero it | [Sequential.lean](code/Samplers/Weighted/Sequential.lean#L26) | [**verified**](SampLib/Samplers/WeightedWithoutReplacement.lean) |
## Integer and weighted sampling / Tables

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.cumulativeChoice` | $\mathrm{Cat}(w)$ | Build cumulative table, then search | [Tables.lean](code/Samplers/Weighted/Tables.lean#L42) | [**verified**](SampLib/Samplers/CumulativeChoice.lean) |
| `Occil.Weighted.cumulativeDraw` | $\mathrm{Cat}(w)$ | Binary search cumulative weights (valid table required) | [Tables.lean](code/Samplers/Weighted/Tables.lean#L30) | [**verified**](SampLib/Samplers/CumulativeDraw.lean) |
| `Occil.Weighted.rationalChoice` | $\mathrm{Cat}(w)$ | Integer-weight sampling construction | [Tables.lean](code/Samplers/Weighted/Tables.lean#L64) | [**verified**](SampLib/Samplers/RationalChoice.lean) |
## Integer and weighted sampling / Trees

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.fastLoadedDiceRoller` | $\mathrm{Cat}(w)$ | Finite dyadic matrix with rejection | [Trees.lean](code/Samplers/Weighted/Trees.lean#L47) | — |
| `Occil.Weighted.hanHoshi` | $\mathrm{Cat}(w)$ | Refine a binary probability interval | [Trees.lean](code/Samplers/Weighted/Trees.lean#L73) | — |
| `Occil.Weighted.knuthYao` | $\mathrm{Cat}(w)$ | Binary probability-matrix leaf walk | [Trees.lean](code/Samplers/Weighted/Trees.lean#L28) | — |
## Integer and weighted sampling / Uniform

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.bitmaskRejection` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Reject out-of-range binary candidates | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L25) | [**verified**](SampLib/Samplers/BitmaskRejection.lean) |
| `Occil.Weighted.fyky` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Upper-interval bit recycling | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L37) | [**verified**](SampLib/Samplers/FYKY.lean) |
| `Occil.Weighted.randomBits` | $\mathrm{Unif}\{0,\ldots,2^k-1\}$ | Concatenate independent fair bits | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L16) | [**verified**](SampLib/Samplers/RandomBits.lean) |
| `Occil.Weighted.recycledSamples` | $\mathrm{Unif}\{0,\ldots,n-1\}^{\otimes k}$ | Repeated uniform draws using one persistent bit-recycling pool | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L71) | — |
| `Occil.Weighted.recycledUniform` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Exact quotient/remainder recycling | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L53) | — |
| `Occil.Weighted.uniformBinaryFloat` | $\text{binary grid uniform approximation}$ | Truncate a leading-zero geometric exponent | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L95) | [**verified**](SampLib/Samplers/UniformBinaryFloat.lean) |
| `Occil.Weighted.uniformDyadic` | $(K,2^b),\ K\sim\mathrm{Unif}\{0,\ldots,2^b-1\}$ | Exact dyadic grid sample: the denominator is 2^bits | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L83) | [**verified**](SampLib/Samplers/UniformFormats.lean) |
| `Occil.Weighted.uniformFixed` | $\mathrm{Unif}\{0,\ldots,s-1\}$ | Fixed-point output uses an explicit integer scale, not an opaque real type | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L88) | [**verified**](SampLib/Samplers/UniformFormats.lean) |
| `Occil.Weighted.uniformRational` | $(K,m),\ K\sim\mathrm{Unif}\{0,\ldots,m-1\}$ | Exact rational grid sample in [0,1): result (numerator,denominator) | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L79) | [**verified**](SampLib/Samplers/UniformFormats.lean) |
## Lazy coin factories

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.arctanFactory` | $\mathrm{Bern}\!\left(\arctan(p)\right)$ | Outer coin and latent-uniform arctangent mixture | [Lazy.lean](code/Samplers/Lazy.lean#L111) | — |
| `Occil.arctanOverPFactory` | $\mathrm{Bern}\!\left(\arctan(p)/p\right)$ | arctan(p)/p, continuously extended to 1 at p=0 | [Lazy.lean](code/Samplers/Lazy.lean#L103) | — |
| `Occil.cosineFactory` | $\mathrm{Bern}\!\left(\cos(p)\right)$ | Cached-uniform cosine-series bounds | [Lazy.lean](code/Samplers/Lazy.lean#L86) | [**verified**](SampLib/Samplers/CosineFactory.lean) |
| `Occil.expMinusMartingale` | $\mathrm{Bern}\!\left(e^{-p}\right)$ | Cached-uniform factorial-series bounds | [Lazy.lean](code/Samplers/Lazy.lean#L83) | [**verified**](SampLib/Samplers/ExpMinusMartingale.lean) |
| `Occil.factorialSeriesFactory` | $\mathrm{Bern}(e^{-p}),\ \mathrm{Bern}(\cos p),\ \mathrm{Bern}(\sin(p)/p)$ | Alternating factorial-series factory | [Lazy.lean](code/Samplers/Lazy.lean#L62) | [**verified**](SampLib/Samplers/FactorialSeriesFactory.lean) |
| `Occil.logOnePlusFactory` | $\mathrm{Bern}\!\left(\log(1+p)\right)$ | ln(1+p) | [Lazy.lean](code/Samplers/Lazy.lean#L94) | [**verified**](SampLib/Samplers/LogOnePlusFactory.lean) |
| `Occil.sampleGeometricBag` | $\mathrm{Bern}(U)\ \text{with shared latent }U$ | Draw Bernoulli(U) from a shared uniform bag: choose a geometrically located digit | [Lazy.lean](code/Samplers/Lazy.lean#L53) | — |
| `Occil.sineFactory` | $\mathrm{Bern}\!\left(\sin(p)\right)$ | Outer coin and sine-series bounds | [Lazy.lean](code/Samplers/Lazy.lean#L89) | [**verified**](SampLib/Samplers/SineFactory.lean) |
## Lazy exact reals / BetaGamma

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.newBeta` | $\mathsf{Lazy}[\mathrm{Beta}(a,b)]$ | Beta PSRN by Occil's geometric-bag power rejection for a,b>=1 | [BetaGamma.lean](code/Samplers/PSRN/BetaGamma.lean#L20) | — |
| `Occil.PSRN.newGamma` | $\mathsf{Lazy}[\mathrm{Gamma}(a,b)]$ | Gamma with arbitrary positive rational shape and rate | [BetaGamma.lean](code/Samplers/PSRN/BetaGamma.lean#L80) | — |
| `Occil.PSRN.newGammaInteger` | $\mathsf{Lazy}[\mathrm{Gamma}(k,\lambda)]$ | Construct a cached lazy real | [BetaGamma.lean](code/Samplers/PSRN/BetaGamma.lean#L60) | — |
| `Occil.PSRN.newGammaMixture` | $\mathsf{Lazy}[\text{Gamma mixture}]$ | Lindley-like mixture of integer-shape gamma PSRNs at a shared rational rate | [BetaGamma.lean](code/Samplers/PSRN/BetaGamma.lean#L67) | — |
| `Occil.PSRN.newLindley` | $\mathsf{Lazy}[\mathrm{Lindley}]$ | Construct a cached lazy real | [BetaGamma.lean](code/Samplers/PSRN/BetaGamma.lean#L73) | — |
## Lazy exact reals / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.coin` | $\mathrm{Bern}(x)\ \text{conditional on cached }x$ | Compare a fresh uniform with cached real | [Core.lean](code/Samplers/PSRN/Core.lean#L100) | — |
| `Occil.PSRN.newInsideShape` | $\mathsf{Lazy}[\mathrm{Unif}(A)]$ | Generic exact rejection inside a cube, for predicates on a list of lazy coordinates | [Core.lean](code/Samplers/PSRN/Core.lean#L105) | — |
| `Occil.PSRN.newRejection` | $\mathsf{Lazy}[\mu(\cdot\mid A)]$ | General lazy proposal/acceptance engine; accepted state is preserved | [Core.lean](code/Samplers/PSRN/Core.lean#L93) | — |
| `Occil.PSRN.newUniform` | $\mathsf{Lazy}[\mathrm{Unif}(0,1)]$ | Construct a cached lazy real | [Core.lean](code/Samplers/PSRN/Core.lean#L43) | — |
## Lazy exact reals / Distributions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.newArcCosine` | $\mathsf{Lazy}[\text{Arc Cosine}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L82) | — |
| `Occil.PSRN.newCauchy` | $\mathsf{Lazy}[\mathrm{Cauchy}]$ | Exact Cauchy by rejection inside the unit disk and a coordinate ratio | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L24) | — |
| `Occil.PSRN.newContinuousBernoulli` | $\mathsf{Lazy}[\text{Continuous Bernoulli}]$ | Continuous Bernoulli(lambda) for rational lambda in (0,1) | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L35) | — |
| `Occil.PSRN.newEpanechnikov` | $\mathsf{Lazy}[\mathrm{Epanechnikov}]$ | Epanechnikov kernel on [-1,1]: twice the median of three uniforms minus one | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L48) | — |
| `Occil.PSRN.newFGMCopula` | $\mathsf{Lazy}[\mathrm{FGMCopula}(\theta)]$ | Farlie–Gumbel–Morgenstern copula by rejection under envelope two | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L55) | — |
| `Occil.PSRN.newGarima` | $\mathsf{Lazy}[\mathrm{Garima}]$ | Named Lindley-family specializations from the PSRN article's mixture table | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L125) | — |
| `Occil.PSRN.newHyperbolicSecant` | $\mathsf{Lazy}[\text{Hyperbolic Secant}]$ | Hyperbolic-secant law in its natural scale, density sech(x)/pi | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L71) | — |
| `Occil.PSRN.newIGarima` | $\mathsf{Lazy}[\text{I Garima}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L128) | — |
| `Occil.PSRN.newMirra` | $\mathsf{Lazy}[\mathrm{Mirra}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L137) | — |
| `Occil.PSRN.newRayleigh` | $\mathsf{Lazy}[\mathrm{Rayleigh}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L18) | — |
| `Occil.PSRN.newRectellipse` | $\mathsf{Lazy}[\mathrm{Rectellipse}]$ | Uniform quarter/full rectellipse, integer radii and rational squareness in [0,1] | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L153) | — |
| `Occil.PSRN.newSushila` | $\mathsf{Lazy}[\mathrm{Sushila}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L142) | — |
| `Occil.PSRN.newTulap` | $\mathsf{Lazy}[\mathrm{Tulap}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L103) | — |
| `Occil.PSRN.newWeightedExponentialGamma` | $\mathsf{Lazy}[\text{Weighted Exponential Gamma}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L131) | — |
| `Occil.PSRN.newXLindley` | $\mathsf{Lazy}[\text{X Lindley}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L147) | — |
| `Occil.PSRN.newXgamma` | $\mathsf{Lazy}[\mathrm{Xgamma}]$ | Construct a cached lazy real | [Distributions.lean](code/Samplers/PSRN/Distributions.lean#L134) | — |
## Lazy exact reals / Exponential

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.expMinusCoin` | $\mathrm{Bern}\!\left(e^{-x}\right)$ | Conditional exp(-x) trial for a nonnegative lazy real x | [Exponential.lean](code/Samplers/PSRN/Exponential.lean#L53) | — |
| `Occil.PSRN.newExponential` | $\mathsf{Lazy}[\mathrm{Exp}(\lambda)]$ | Exponential PSRN at an arbitrary positive rational rate | [Exponential.lean](code/Samplers/PSRN/Exponential.lean#L32) | — |
| `Occil.PSRN.newExponentialFromDecay` | $\mathsf{Lazy}[\mathrm{Exp}(\lambda)]$ | An e-rand from exact exp(-rate/d) coins | [Exponential.lean](code/Samplers/PSRN/Exponential.lean#L19) | — |
| `Occil.PSRN.newExponentialLogRate` | $\mathsf{Lazy}[\mathrm{Exp}(\log(x/y))]$ | Exponential PSRN with rate ln(x/y), x>y>0 | [Exponential.lean](code/Samplers/PSRN/Exponential.lean#L39) | — |
| `Occil.PSRN.newExponentialUnknownRate` | $\mathsf{Lazy}[\mathrm{Exp}(p)]$ | Exponential PSRN with unknown positive rate p<=1 supplied as a p-coin | [Exponential.lean](code/Samplers/PSRN/Exponential.lean#L46) | — |
## Lazy exact reals / Gaussian

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.newGaussian` | $\mathsf{Lazy}[\mathcal N(0,1)]$ | Exact standard normal represented as a lazy interval oracle | [Gaussian.lean](code/Samplers/PSRN/Gaussian.lean#L31) | — |
| `Occil.PSRN.newNormal` | $\mathsf{Lazy}[\mathcal N(\mu,\sigma^2)]$ | Construct a cached lazy real | [Gaussian.lean](code/Samplers/PSRN/Gaussian.lean#L46) | — |
## Lazy exact reals / Geometry

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.newBall` | $\mathsf{Lazy}[\mathrm{Unif}(B^d)]$ | Uniform volume measure on a unit ball | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L45) | — |
| `Occil.PSRN.newDirichlet` | $\mathsf{Lazy}[\mathrm{Dirichlet}(\alpha)]$ | Construct a cached lazy real | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L68) | — |
| `Occil.PSRN.newShell` | $\mathsf{Lazy}[\mathrm{Unif}(\text{spherical shell})]$ | Uniform shell with positive rational outer radius and nonnegative inner radius | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L54) | — |
| `Occil.PSRN.newSimplex` | $\mathsf{Lazy}[\mathrm{Unif}(\Delta_d)]$ | Uniform positive components summing to one, via independent exponentials | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L91) | — |
| `Occil.PSRN.newSphere` | $\mathsf{Lazy}[\mathrm{Unif}(S^{d-1})]$ | Uniform surface measure on the unit sphere in the requested dimension | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L34) | — |
## Lazy exact reals / Uniform

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.newByDigits` | $\mathsf{Lazy}[\text{digit-oracle real}]$ | A generic memoized digit sampler | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L52) | — |
| `Occil.PSRN.newOddsUniform` | $\mathsf{Lazy}[U/(1-U)]$ | Construct a cached lazy real | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L87) | — |
| `Occil.PSRN.newOrderStatistic` | $\mathsf{Lazy}[\mathrm{Beta}(k,n+1-k)]$ | Select k-th of n independent lazy uniforms without filling unsampled tails | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L19) | — |
| `Occil.PSRN.newPowerUniform` | $\mathsf{Lazy}[U^{a/b}]$ | Uniform raised to a rational power; negative powers have unbounded tails | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L32) | — |
| `Occil.PSRN.newRatioUniforms` | $\mathsf{Lazy}[U/V]$ | Construct a cached lazy real | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L77) | — |
| `Occil.PSRN.newReciprocalPowerUniform` | $\mathsf{Lazy}[U^{-a/b}]$ | Construct a cached lazy real | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L83) | — |
| `Occil.PSRN.newReciprocalUniform` | $\mathsf{Lazy}[1/U]$ | Construct a cached lazy real | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L80) | — |
| `Occil.PSRN.newUniformSum` | $\mathsf{Lazy}[\sum_{i=1}^nU_i]$ | Construct a cached lazy real | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L72) | — |
| `Occil.PSRN.powerCoin` | $\mathrm{Bern}\!\left(p^{a/b}\right)$ | Raise an abstract coin's probability to a nonnegative rational power | [Uniform.lean](code/Samplers/PSRN/Uniform.lean#L39) | — |
## Numerical arithmetic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numeric.coin` | $\mathrm{Bern}(a/s)$ | Rational coin at the supplied grid probability | [Numeric.lean](code/Samplers/Numeric.lean#L244) | — |
| `Occil.Numeric.uniform` | $\mathrm{Unif}\{1,\ldots,s-1\}$ | Interior grid uniform: integers 1,...,scale-1 | [Numeric.lean](code/Samplers/Numeric.lean#L239) | — |
## Numerical grid algorithms / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.exponential` | $\mathsf{Grid}_s[\mathrm{exponential}]$ | Inverse transform using a grid logarithm | [Core.lean](code/Samplers/Numerical/Core.lean#L28) | — |
| `Occil.Numerical.uniformRange` | $\mathsf{Grid}_s[\text{uniform Range}]$ | Numerical uniform on [lo,hi); a narrow interval can quantize to its lower endpoint | [Core.lean](code/Samplers/Numerical/Core.lean#L22) | — |
## Numerical grid algorithms / Densities

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.hyperexponential` | $\mathsf{Grid}_s[\mathrm{hyperexponential}]$ | Hyperexponential: integer mixture weights and fixed-point component rates | [Densities.lean](code/Samplers/Numerical/Densities.lean#L23) | — |
| `Occil.Numerical.hypoexponential` | $\mathsf{Grid}_s[\mathrm{hypoexponential}]$ | Hypoexponential: sum of independent exponentials with the supplied positive rates | [Densities.lean](code/Samplers/Numerical/Densities.lean#L18) | — |
| `Occil.Numerical.piecewiseConstant` | $\mathsf{Grid}_s[\text{piecewise Constant}]$ | Area-weighted bin and scaled uniform | [Densities.lean](code/Samplers/Numerical/Densities.lean#L57) | — |
| `Occil.Numerical.piecewiseLinear` | $\mathsf{Grid}_s[\text{piecewise Linear}]$ | Area-weighted rectangle/triangle mixture | [Densities.lean](code/Samplers/Numerical/Densities.lean#L32) | — |
| `Occil.Numerical.sinePower` | $\mathsf{Grid}_s[\text{sine Power}]$ | Sine-power density on [0,pi], using the beta-envelope rejection in the index | [Densities.lean](code/Samplers/Numerical/Densities.lean#L72) | — |
## Numerical grid algorithms / DistributionFamilies

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Specialized.alphaPowerTransformed` | $\mathsf{Grid}_s[\text{alpha Power Transformed}]$ | Logarithmic parameter transform of Exp-G | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L28) | — |
| `Occil.Specialized.biweightG` | $\mathsf{Grid}_s[\text{biweight G}]$ | Biweight rejection before quantile transformation | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L63) | — |
| `Occil.Specialized.cdfQuantileFamily` | $\mathsf{Grid}_s[\text{cdf Quantile Family}]$ | Smithson–Shou CDF–quantile family | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L131) | — |
| `Occil.Specialized.cubicRankTransmuted` | $\mathsf{Grid}_s[\text{cubic Rank Transmuted}]$ | Weighted ranks of three uniforms | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L46) | — |
| `Occil.Specialized.expG` | $\mathsf{Grid}_s[\text{exp G}]$ | Exponential probability transform and quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L19) | — |
| `Occil.Specialized.exponentiatedG` | $\mathsf{Grid}_s[\text{exponentiated G}]$ | Power-transform a uniform before quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L32) | — |
| `Occil.Specialized.generalizedGammaG` | $\mathsf{Grid}_s[\text{generalized Gamma G}]$ | Exponentiated generalized-gamma before quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L100) | — |
| `Occil.Specialized.inflatedDistribution` | $\mathsf{Grid}_s[\text{inflated Distribution}]$ | Choose atom or supplied distribution | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L115) | — |
| `Occil.Specialized.inverseDistribution` | $\mathsf{Grid}_s[\text{inverse Distribution}]$ | Reciprocate a supplied sample | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L105) | — |
| `Occil.Specialized.oddLogLogisticG` | $\mathsf{Grid}_s[\text{odd Log Logistic G}]$ | Powered odds before quantile transformation | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L83) | — |
| `Occil.Specialized.oddXG` | $\mathsf{Grid}_s[\text{odd X G}]$ | Odds compression before quantile transformation | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L78) | — |
| `Occil.Specialized.rayleighG` | $\mathsf{Grid}_s[\text{rayleigh G}]$ | Exponentiated negative Rayleigh before quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L89) | — |
| `Occil.Specialized.rayleighRayleigh` | $\mathsf{Grid}_s[\text{rayleigh Rayleigh}]$ | Rayleigh-G with a Rayleigh quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L93) | — |
| `Occil.Specialized.tRY` | $\mathsf{Grid}_s[\text{t R Y}]$ | Component CDF followed by target quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L74) | — |
| `Occil.Specialized.transformedTransformer` | $\mathsf{Grid}_s[\text{transformed Transformer}]$ | Compose sample, inverse transform, and quantile | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L70) | — |
| `Occil.Specialized.transmutedG` | $\mathsf{Grid}_s[\text{transmuted G}]$ | Mixture of uniform and extreme ranks | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L37) | — |
| `Occil.Specialized.unitDistribution` | $\mathsf{Grid}_s[\text{unit Distribution}]$ | Exponentiate negative supplied sample | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L125) | — |
| `Occil.Specialized.weightedDistribution` | $\mathsf{Grid}_s[\text{weighted Distribution}]$ | Rejection weighting; weight x must be a probability in [0,scale] | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L110) | — |
| `Occil.Specialized.xG` | $\mathsf{Grid}_s[\text{x G}]$ | Apply quantile to a component sample | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L16) | — |
| `Occil.Specialized.zeroOneInflated` | $\mathsf{Grid}_s[\text{zero One Inflated}]$ | Choose endpoint atom or supplied distribution | [DistributionFamilies.lean](code/Samplers/Numerical/DistributionFamilies.lean#L119) | — |
## Numerical grid algorithms / Gamma

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.beta` | $\mathsf{Grid}_s[\mathrm{beta}]$ | Ratio of two numerical gamma draws | [Gamma.lean](code/Samplers/Numerical/Gamma.lean#L45) | — |
| `Occil.Numerical.gamma` | $\mathsf{Grid}_s[\mathrm{gamma}]$ | Marsaglia–Tsang rejection and shape augmentation | [Gamma.lean](code/Samplers/Numerical/Gamma.lean#L18) | — |
| `Occil.Numerical.gammaSmallShape` | $\mathsf{Grid}_s[\text{gamma Small Shape}]$ | Liu–Martin–Syring small-shape rejection | [Gamma.lean](code/Samplers/Numerical/Gamma.lean#L60) | — |
## Numerical grid algorithms / GammaFamilies

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.amoroso` | $\mathsf{Grid}_s[\mathrm{amoroso}]$ | Location–scale generalized-gamma construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L143) | — |
| `Occil.Numerical.arcsine` | $\mathsf{Grid}_s[\mathrm{arcsine}]$ | Symmetric half-shape beta construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L95) | — |
| `Occil.Numerical.betaPERT` | $\mathsf{Grid}_s[\text{beta P E R T}]$ | Rescale a mode-parameterized beta draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L58) | — |
| `Occil.Numerical.betaPrime` | $\mathsf{Grid}_s[\text{beta Prime}]$ | Power-transform a ratio of gamma draws | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L51) | — |
| `Occil.Numerical.chi` | $\mathsf{Grid}_s[\mathrm{chi}]$ | Square root of chi-square draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L71) | — |
| `Occil.Numerical.chiSquared` | $\mathsf{Grid}_s[\text{chi Squared}]$ | Scale a half-shape gamma draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L17) | — |
| `Occil.Numerical.dagum` | $\mathsf{Grid}_s[\mathrm{dagum}]$ | Unit-denominator-shape beta-prime construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L152) | — |
| `Occil.Numerical.fisherF` | $\mathsf{Grid}_s[\text{fisher F}]$ | Ratio of normalized chi-square draws | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L34) | — |
| `Occil.Numerical.generalizedGamma` | $\mathsf{Grid}_s[\text{generalized Gamma}]$ | Power and rescale a gamma draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L107) | — |
| `Occil.Numerical.generalizedInverseGamma` | $\mathsf{Grid}_s[\text{generalized Inverse Gamma}]$ | Reciprocate a generalized-gamma draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L113) | — |
| `Occil.Numerical.generalizedNormal` | $\mathsf{Grid}_s[\text{generalized Normal}]$ | Generalized normal / exponential-power density proportional to exp(-&#124;x&#124;^shape) | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L99) | — |
| `Occil.Numerical.inverseChiSquared` | $\mathsf{Grid}_s[\text{inverse Chi Squared}]$ | Reciprocate a normalized chi-square draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L74) | — |
| `Occil.Numerical.inverseGamma` | $\mathsf{Grid}_s[\text{inverse Gamma}]$ | Reciprocate and scale a gamma draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L42) | — |
| `Occil.Numerical.kumaraswamy` | $\mathsf{Grid}_s[\mathrm{kumaraswamy}]$ | Power-transform a unit-shape beta draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L46) | — |
| `Occil.Numerical.levy` | $\mathsf{Grid}_s[\mathrm{levy}]$ | Reciprocate a half-shape gamma draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L77) | — |
| `Occil.Numerical.logLogistic` | $\mathsf{Grid}_s[\text{log Logistic}]$ | Unit-shape beta-prime construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L155) | — |
| `Occil.Numerical.maxUniform` | $\mathsf{Grid}_s[\text{max Uniform}]$ | Unit-second-shape beta construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L162) | — |
| `Occil.Numerical.maxwell` | $\mathsf{Grid}_s[\mathrm{maxwell}]$ | Square root of a gamma draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L82) | — |
| `Occil.Numerical.minUniform` | $\mathsf{Grid}_s[\text{min Uniform}]$ | Unit-first-shape beta construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L159) | — |
| `Occil.Numerical.noncentralBeta` | $\mathsf{Grid}_s[\text{noncentral Beta}]$ | Poisson mixture of beta shapes | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L65) | — |
| `Occil.Numerical.noncentralChiSquared` | $\mathsf{Grid}_s[\text{noncentral Chi Squared}]$ | Noncentral chi-square via a Poisson mixture; noncentrality is sum of mean squares | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L22) | — |
| `Occil.Numerical.parabolic` | $\mathsf{Grid}_s[\mathrm{parabolic}]$ | Symmetric Beta(2,2) construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L92) | — |
| `Occil.Numerical.pearsonVI` | $\mathsf{Grid}_s[\text{pearson V I}]$ | Unit-power beta-prime construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L146) | — |
| `Occil.Numerical.powerDistribution` | $\mathsf{Grid}_s[\text{power Distribution}]$ | Main-index power distribution: Beta(shape,1)/domain; domain is an inverse scale | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L118) | — |
| `Occil.Numerical.powerFunction` | $\mathsf{Grid}_s[\text{power Function}]$ | Rescale a unit-second-shape beta draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L135) | — |
| `Occil.Numerical.singhMaddala` | $\mathsf{Grid}_s[\text{singh Maddala}]$ | Unit-numerator-shape beta-prime construction | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L149) | — |
| `Occil.Numerical.stacy` | $\mathsf{Grid}_s[\mathrm{stacy}]$ | Gamma-mixture names appearing in the main distribution index | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L140) | — |
| `Occil.Numerical.studentT` | $\mathsf{Grid}_s[\text{student T}]$ | Normal divided by chi-square scale | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L28) | — |
| `Occil.Numerical.twinT` | $\mathsf{Grid}_s[\text{twin T}]$ | Twin-t rejection | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L124) | — |
| `Occil.Numerical.wignerSemicircle` | $\mathsf{Grid}_s[\text{wigner Semicircle}]$ | Affine transform of a beta draw | [GammaFamilies.lean](code/Samplers/Numerical/GammaFamilies.lean#L87) | — |
## Numerical grid algorithms / Mixtures

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Specialized.asymmetricGeneralizedGaussian` | $\mathsf{Grid}_s[\text{asymmetric Generalized Gaussian}]$ | Two-piece generalized-normal construction | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L100) | — |
| `Occil.Specialized.erlangMixture` | $\mathsf{Grid}_s[\text{erlang Mixture}]$ | Numerical Erlang mixture | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L19) | — |
| `Occil.Specialized.extendedXgamma` | $\mathsf{Grid}_s[\text{extended Xgamma}]$ | Randomly increment the gamma shape | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L72) | — |
| `Occil.Specialized.gammaExponential` | $\mathsf{Grid}_s[\text{gamma Exponential}]$ | Ratio of independent powered gamma draws | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L63) | — |
| `Occil.Specialized.garima` | $\mathsf{Grid}_s[\mathrm{garima}]$ | Garima-weighted gamma shape mixture | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L29) | — |
| `Occil.Specialized.iGarima` | $\mathsf{Grid}_s[\text{i Garima}]$ | Modified Garima gamma shape mixture | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L34) | — |
| `Occil.Specialized.lindley` | $\mathsf{Grid}_s[\mathrm{lindley}]$ | Mixture of gamma shapes one and two | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L25) | — |
| `Occil.Specialized.logarithmicSkewNormal` | $\mathsf{Grid}_s[\text{logarithmic Skew Normal}]$ | Exponentiate a shifted skew-normal draw | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L85) | — |
| `Occil.Specialized.mirra` | $\mathsf{Grid}_s[\mathrm{mirra}]$ | Parameter-weighted gamma shape mixture | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L47) | — |
| `Occil.Specialized.offsetSymmetricGaussian` | $\mathsf{Grid}_s[\text{offset Symmetric Gaussian}]$ | Truncated shifted normal magnitude and sign | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L105) | — |
| `Occil.Specialized.skewSymmetric` | $\mathsf{Grid}_s[\text{skew Symmetric}]$ | Generic skew-symmetric construction; both callbacks return numerical values | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L80) | — |
| `Occil.Specialized.sushila` | $\mathsf{Grid}_s[\mathrm{sushila}]$ | Rescale a Lindley mixture draw | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L53) | — |
| `Occil.Specialized.suzuki` | $\mathsf{Grid}_s[\mathrm{suzuki}]$ | Suzuki mixture: a Rayleigh variate whose scale is independently lognormal | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L133) | — |
| `Occil.Specialized.tiltedBeta` | $\mathsf{Grid}_s[\text{tilted Beta}]$ | Mixture of beta and tilted-uniform rejection | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L114) | — |
| `Occil.Specialized.tiltedBetaBinomial` | $\mathsf{Grid}_s[\text{tilted Beta Binomial}]$ | n is an ordinary integer count, the other parameters are fixed point | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L125) | — |
| `Occil.Specialized.twoPiece` | $\mathsf{Grid}_s[\text{two Piece}]$ | Two-piece family, from an arbitrary symmetric numerical sampler | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L92) | — |
| `Occil.Specialized.weightedExponentialGamma` | $\mathsf{Grid}_s[\text{weighted Exponential Gamma}]$ | Mixture of gamma shapes two and three | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L39) | — |
| `Occil.Specialized.xLindley` | $\mathsf{Grid}_s[\text{x Lindley}]$ | Mixture of exponential and Lindley draws | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L57) | — |
| `Occil.Specialized.xgamma` | $\mathsf{Grid}_s[\mathrm{xgamma}]$ | Mixture of gamma shapes one and three | [Mixtures.lean](code/Samplers/Numerical/Mixtures.lean#L43) | — |
## Numerical grid algorithms / Normal

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.birnbaumSaunders` | $\mathsf{Grid}_s[\text{birnbaum Saunders}]$ | Square a transformed normal draw | [Normal.lean](code/Samplers/Numerical/Normal.lean#L93) | — |
| `Occil.Numerical.generalizedSkewNormal` | $\mathsf{Grid}_s[\text{generalized Skew Normal}]$ | The selection construction for generalized skew-normal SNE(lambda,xi) | [Normal.lean](code/Samplers/Numerical/Normal.lean#L113) | — |
| `Occil.Numerical.generalizedSkewNormalConditional` | $\mathsf{Grid}_s[\text{generalized Skew Normal Conditional}]$ | Conditional-normal SNE(lambda,xi) construction, distinct from selection rejection | [Normal.lean](code/Samplers/Numerical/Normal.lean#L177) | — |
| `Occil.Numerical.halfNormal` | $\mathsf{Grid}_s[\text{half Normal}]$ | Absolute value of a normal draw | [Normal.lean](code/Samplers/Numerical/Normal.lean#L90) | — |
| `Occil.Numerical.inverseGaussian` | $\mathsf{Grid}_s[\text{inverse Gaussian}]$ | Michael–Schucany–Haas inverse Gaussian, mean and shape strictly positive | [Normal.lean](code/Samplers/Numerical/Normal.lean#L76) | — |
| `Occil.Numerical.lognormal` | $\mathsf{Grid}_s[\mathrm{lognormal}]$ | Exponentiate a numerical normal draw | [Normal.lean](code/Samplers/Numerical/Normal.lean#L72) | — |
| `Occil.Numerical.moyal` | $\mathsf{Grid}_s[\mathrm{moyal}]$ | Moyal from -log(Z^2), Z standard normal | [Normal.lean](code/Samplers/Numerical/Normal.lean#L120) | — |
| `Occil.Numerical.normal` | $\mathsf{Grid}_s[\mathrm{normal}]$ | First coordinate of polar construction | [Normal.lean](code/Samplers/Numerical/Normal.lean#L40) | — |
| `Occil.Numerical.normalBoxMuller` | $\mathsf{Grid}_s[\mathcal N(\mu,\sigma^2)^{\otimes2}]$ | Box–Muller trigonometric transform | [Normal.lean](code/Samplers/Numerical/Normal.lean#L17) | — |
| `Occil.Numerical.normalCLT` | $\mathsf{Grid}_s[\text{normal C L T}]$ | Sum twelve centered grid uniforms | [Normal.lean](code/Samplers/Numerical/Normal.lean#L64) | — |
| `Occil.Numerical.normalCLTK` | $\mathsf{Grid}_s[\text{normal C L T K}]$ | Normalize a sum of grid uniforms | [Normal.lean](code/Samplers/Numerical/Normal.lean#L152) | — |
| `Occil.Numerical.normalCLTWarped` | $\mathsf{Grid}_s[\text{normal C L T Warped}]$ | Polynomial correction to twelve-uniform approximation | [Normal.lean](code/Samplers/Numerical/Normal.lean#L141) | — |
| `Occil.Numerical.normalInversion` | $\mathsf{Grid}_s[\mathrm{normal}]$ | Approximate normal-CDF inversion | [Normal.lean](code/Samplers/Numerical/Normal.lean#L57) | — |
| `Occil.Numerical.normalPolar` | $\mathsf{Grid}_s[\mathcal N(\mu,\sigma^2)^{\otimes2}]$ | Marsaglia polar rejection | [Normal.lean](code/Samplers/Numerical/Normal.lean#L27) | — |
| `Occil.Numerical.normalRatioOfUniforms` | $\mathsf{Grid}_s[\mathrm{normal}]$ | Ratio-of-uniforms rejection | [Normal.lean](code/Samplers/Numerical/Normal.lean#L44) | — |
| `Occil.Numerical.powerLognormal` | $\mathsf{Grid}_s[\text{power Lognormal}]$ | Exponentiate a power-normal draw | [Normal.lean](code/Samplers/Numerical/Normal.lean#L136) | — |
| `Occil.Numerical.powerNormal` | $\mathsf{Grid}_s[\text{power Normal}]$ | Power-transformed uniform and normal quantile | [Normal.lean](code/Samplers/Numerical/Normal.lean#L128) | — |
| `Occil.Numerical.qGaussian` | $\mathsf{Grid}_s[\text{q Gaussian}]$ | Generalized Box–Muller q-Gaussian pair, q<3 | [Normal.lean](code/Samplers/Numerical/Normal.lean#L161) | — |
| `Occil.Numerical.skewNormal` | $\mathsf{Grid}_s[\text{skew Normal}]$ | Azzalini skew-normal construction from two independent standard normals | [Normal.lean](code/Samplers/Numerical/Normal.lean#L101) | — |
| `Occil.Numerical.skewNormalExtremes` | $\mathsf{Grid}_s[\text{skew Normal Extremes}]$ | Weighted combination of normal minimum and maximum | [Normal.lean](code/Samplers/Numerical/Normal.lean#L195) | — |
## Numerical grid algorithms / SpecialDistributions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Specialized.arcCosine` | $\mathsf{Grid}_s[\text{arc Cosine}]$ | CDF 1-cos(pi*x/2), x in [0,1], inverted with atan and sqrt | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L50) | — |
| `Occil.Specialized.continuousBernoulli` | $\mathsf{Grid}_s[\text{continuous Bernoulli}]$ | Continuous Bernoulli by numerical inverse CDF; endpoints are limiting atoms | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L98) | — |
| `Occil.Specialized.cosine` | $\mathsf{Grid}_s[\mathrm{cosine}]$ | Main-index cosine distribution on [-1/2,1/2], via asin(U)/pi | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L182) | — |
| `Occil.Specialized.epanechnikov` | $\mathsf{Grid}_s[\mathrm{epanechnikov}]$ | Devroye–Györfi's three-uniform Epanechnikov construction on [-1,1] | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L24) | — |
| `Occil.Specialized.exponentialLogRate` | $\mathsf{Grid}_s[\text{exponential Log Rate}]$ | Exponential draw with logarithmic rate | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L57) | — |
| `Occil.Specialized.generalizedPareto` | $\mathsf{Grid}_s[\text{generalized Pareto}]$ | Generalized-Pareto inverse uniform transform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L151) | — |
| `Occil.Specialized.hyperbolicSecant` | $\mathsf{Grid}_s[\text{hyperbolic Secant}]$ | Hyperbolic secant density sech(x)/pi, by numerical inversion | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L18) | — |
| `Occil.Specialized.lehmannWeibull` | $\mathsf{Grid}_s[\text{lehmann Weibull}]$ | Power and scale an exponential draw | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L116) | — |
| `Occil.Specialized.lomax` | $\mathsf{Grid}_s[\mathrm{lomax}]$ | Shift and power-transform a uniform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L135) | — |
| `Occil.Specialized.marshallOlkin` | $\mathsf{Grid}_s[\text{marshall Olkin}]$ | Rational transform of a grid uniform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L123) | — |
| `Occil.Specialized.powerFunction` | $\mathsf{Grid}_s[\text{power Function}]$ | Rescale a power of a grid uniform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L110) | — |
| `Occil.Specialized.powerLomax` | $\mathsf{Grid}_s[\text{power Lomax}]$ | Power-transform a Lomax draw | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L140) | — |
| `Occil.Specialized.quarterRectellipse` | $\mathsf{Grid}_s[\text{quarter Rectellipse}]$ | Reject rectangle proposals by implicit boundary | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L159) | — |
| `Occil.Specialized.ratioUniforms` | $\mathsf{Grid}_s[\text{ratio Uniforms}]$ | Ratio of two independent grid uniforms | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L32) | — |
| `Occil.Specialized.reciprocalPowerUniform` | $\mathsf{Grid}_s[\text{reciprocal Power Uniform}]$ | Negative power of a grid uniform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L39) | — |
| `Occil.Specialized.reciprocalUniform` | $\mathsf{Grid}_s[\text{reciprocal Uniform}]$ | Reciprocate an interior grid uniform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L36) | — |
| `Occil.Specialized.rectellipse` | $\mathsf{Grid}_s[\mathrm{rectellipse}]$ | Reflect quarter-rectellipse coordinates by fair signs | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L173) | — |
| `Occil.Specialized.slash` | $\mathsf{Grid}_s[\mathrm{slash}]$ | Divide normal by independent grid uniform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L129) | — |
| `Occil.Specialized.toppLeone` | $\mathsf{Grid}_s[\text{topp Leone}]$ | Complementary square-root uniform transform | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L145) | — |
| `Occil.Specialized.tulap` | $\mathsf{Grid}_s[\mathrm{tulap}]$ | Tulap(location,b,q) | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L85) | — |
| `Occil.Specialized.uniformOdds` | $\mathsf{Grid}_s[\text{uniform Odds}]$ | Divide a uniform by its complement | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L44) | — |
## Numerical grid algorithms / StoppedDistributions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Specialized.bivariateExponentialGeometric` | $\mathsf{Grid}_s[\text{bivariate Exponential Geometric}]$ | Return geometric-stopped exponential sum and count | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L53) | — |
| `Occil.Specialized.bivariateGammaGeometric` | $\mathsf{Grid}_s[\text{bivariate Gamma Geometric}]$ | Gamma/geometric episode: return (sum, number of summands) | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L47) | — |
| `Occil.Specialized.exponentialPoisson` | $\mathsf{Grid}_s[\text{exponential Poisson}]$ | Poisson-stopped minimum of exponential draws | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L26) | — |
| `Occil.Specialized.geometricZeroTruncatedPoisson` | $\mathsf{Grid}_s[\text{geometric Zero Truncated Poisson}]$ | Poisson-stopped maximum of geometric draws | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L20) | — |
| `Occil.Specialized.gmdp` | $\mathsf{Grid}_s[\mathrm{gmdp}]$ | GMDP episode: gamma summands, a discrete-Pareto stopping count | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L72) | — |
| `Occil.Specialized.grassia` | $\mathsf{Grid}_s[\mathrm{grassia}]$ | Exponentiate negative gamma draw | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L67) | — |
| `Occil.Specialized.poissonExponential` | $\mathsf{Grid}_s[\text{poisson Exponential}]$ | Poisson-stopped maximum of exponential draws | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L32) | — |
| `Occil.Specialized.rightTruncatedWeibull` | $\mathsf{Grid}_s[\text{right Truncated Weibull}]$ | Poisson-stopped minimum of power-function draws | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L38) | — |
| `Occil.Specialized.unitLindley` | $\mathsf{Grid}_s[\text{unit Lindley}]$ | Odds compression of a Lindley draw | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L57) | — |
| `Occil.Specialized.zeroOneInflatedUnitLindley` | $\mathsf{Grid}_s[\text{zero One Inflated Unit Lindley}]$ | Endpoint atoms mixed with unit Lindley | [StoppedDistributions.lean](code/Samplers/Numerical/StoppedDistributions.lean#L62) | — |
## Numerical grid algorithms / Univariate

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.bates` | $\mathsf{Grid}_s[\mathrm{bates}]$ | Average independent grid uniforms | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L144) | — |
| `Occil.Numerical.cauchy` | $\mathsf{Grid}_s[\mathrm{cauchy}]$ | Tangent transform of a grid angle | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L29) | — |
| `Occil.Numerical.cauchyDisk` | $\mathsf{Grid}_s[\text{cauchy Disk}]$ | Ratio of coordinates from disk rejection | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L37) | — |
| `Occil.Numerical.doubleLogarithmic` | $\mathsf{Grid}_s[\text{double Logarithmic}]$ | Center and sign a uniform product | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L139) | — |
| `Occil.Numerical.frechet` | $\mathsf{Grid}_s[\mathrm{frechet}]$ | Negative power of a numerical exponential | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L80) | — |
| `Occil.Numerical.generalizedExtremeValue` | $\mathsf{Grid}_s[\text{generalized Extreme Value}]$ | GEV parameterization used in Occil's index: (E^(-shape)-1)/shape | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L72) | — |
| `Occil.Numerical.generalizedTukeyLambda` | $\mathsf{Grid}_s[\text{generalized Tukey Lambda}]$ | Asymmetric uniform power transforms | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L114) | — |
| `Occil.Numerical.gumbel` | $\mathsf{Grid}_s[\mathrm{gumbel}]$ | Log-transform a numerical exponential | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L66) | — |
| `Occil.Numerical.laplace` | $\mathsf{Grid}_s[\mathrm{laplace}]$ | Sign and rescale a numerical exponential | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L16) | — |
| `Occil.Numerical.logarithmicProduct` | $\mathsf{Grid}_s[\text{logarithmic Product}]$ | Multiply two independent grid uniforms | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L136) | — |
| `Occil.Numerical.logistic` | $\mathsf{Grid}_s[\mathrm{logistic}]$ | Log-odds transform of a grid uniform | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L22) | — |
| `Occil.Numerical.pareto` | $\mathsf{Grid}_s[\mathrm{pareto}]$ | Negative power of a grid uniform | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L55) | — |
| `Occil.Numerical.powerLaw` | $\mathsf{Grid}_s[\text{power Law}]$ | Ordinary power law on a finite positive interval, with density proportional to x^exponent | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L124) | — |
| `Occil.Numerical.rayleigh` | $\mathsf{Grid}_s[\mathrm{rayleigh}]$ | Square root of a scaled exponential | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L61) | — |
| `Occil.Numerical.triangular` | $\mathsf{Grid}_s[\mathrm{triangular}]$ | Triangular on [lo,hi], with mode between the endpoints | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L87) | — |
| `Occil.Numerical.triangularUniforms` | $\mathsf{Grid}_s[\text{triangular Uniforms}]$ | Stein–Keblis family (1-alpha)*min(U,V)+alpha*max(U,V), alpha in [0,1] | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L98) | — |
| `Occil.Numerical.tukeyLambda` | $\mathsf{Grid}_s[\text{tukey Lambda}]$ | Difference of uniform power transforms | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L107) | — |
| `Occil.Numerical.weibull` | $\mathsf{Grid}_s[\mathrm{weibull}]$ | Power-transform a numerical exponential | [Univariate.lean](code/Samplers/Numerical/Univariate.lean#L49) | — |
## Numerical multivariate algorithms / Copulas

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.archimedeanCopula` | $\mathsf{Grid}_s[\text{archimedean Copula}]$ | Marshall-Olkin frailty construction for a completely monotone Archimedean Laplace generator | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L122) | — |
| `Occil.Multivariate.beckmann` | $\mathsf{Grid}_s[\mathrm{beckmann}]$ | Norm of a correlated Gaussian pair | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L144) | — |
| `Occil.Multivariate.claytonCopula` | $\mathsf{Grid}_s[\text{clayton Copula}]$ | Gamma frailty and Archimedean generator | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L129) | — |
| `Occil.Multivariate.complexNormal` | $\mathsf{Grid}_s[\text{complex Normal}]$ | Independent normal real and imaginary components | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L162) | — |
| `Occil.Multivariate.correlatedExponential` | $\mathsf{Grid}_s[\text{correlated Exponential}]$ | Gaussian copula and exponential quantiles | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L48) | — |
| `Occil.Multivariate.elliptical` | $\mathsf{Grid}_s[\mathrm{elliptical}]$ | Elliptical family with an independent radius callback and covariance shape | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L138) | — |
| `Occil.Multivariate.exchangeableFGMCopula` | $\mathsf{Grid}_s[\text{exchangeable F G M Copula}]$ | FGM latent-bit construction: sqrt(V)*W^I | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L204) | — |
| `Occil.Multivariate.exchangeableFGMSource` | $\mathsf{Grid}_s[\text{exchangeable F G M Source}]$ | Literal max/min recipe printed in exporand.html | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L191) | — |
| `Occil.Multivariate.exchangeableLabels` | $\mathsf{Grid}_s[\text{exchangeable Labels}]$ | Exchangeable binary labels with the prescribed count weights | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L181) | — |
| `Occil.Multivariate.gaussianCopula` | $\mathsf{Grid}_s[\text{gaussian Copula}]$ | Gaussian copula from any positive-definite covariance matrix | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L12) | — |
| `Occil.Multivariate.gumbelCopula` | $\mathsf{Grid}_s[\text{gumbel Copula}]$ | Gumbel-Hougaard copula, theta>=1, using a positive stable frailty | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L169) | — |
| `Occil.Multivariate.lowerBoundCopula` | $(U,s-U),\ U\sim\mathrm{Unif}\{1,\ldots,s-1\}$ | Pair a grid uniform with its complement | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L32) | — |
| `Occil.Multivariate.normalToAnything` | $\mathsf{Grid}_s[\text{normal To Anything}]$ | Gaussian-copula dependence followed by arbitrary quantile callbacks | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L44) | — |
| `Occil.Multivariate.poissonHierarchy` | $\mathsf{Grid}_s[\text{poisson Hierarchy}]$ | Bivariate T-Poisson hierarchy with Gaussian/exponential latent dependence | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L60) | — |
| `Occil.Multivariate.poissonHierarchyND` | $\mathsf{Grid}_s[\text{poisson Hierarchy N D}]$ | N-dimensional copula/quantile Poisson hierarchy | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L69) | — |
| `Occil.Multivariate.productCopula` | $\mathrm{Unif}\{1,\ldots,s-1\}^{\otimes d}$ | Independent interior grid uniforms | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L23) | — |
| `Occil.Multivariate.rice` | $\mathsf{Grid}_s[\mathrm{rice}]$ | Equal-variance Beckmann specialization | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L149) | — |
| `Occil.Multivariate.riceNorton` | $\mathsf{Grid}_s[\text{rice Norton}]$ | Norm of three shifted normal draws | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L154) | — |
| `Occil.Multivariate.studentT` | $\mathsf{Grid}_s[\text{student T}]$ | Shared chi-square scales a Gaussian vector | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L80) | — |
| `Occil.Multivariate.studentTCopula` | $\mathsf{Grid}_s[\text{student T Copula}]$ | Student vector followed by marginal CDFs | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L108) | — |
| `Occil.Multivariate.upperBoundCopula` | $(U,\ldots,U),\ U\sim\mathrm{Unif}\{1,\ldots,s-1\}$ | Repeat one shared grid uniform | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L27) | — |
## Numerical multivariate algorithms / Geometry

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.ball` | $\mathsf{Grid}_s[\mathrm{ball}]$ | Sphere direction and independent uniform-power radius | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L64) | — |
| `Occil.Multivariate.ballEPD` | $\mathsf{Grid}_s[\text{ball E P D}]$ | EPD/exponential construction of a uniform finite-p ball | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L74) | — |
| `Occil.Multivariate.betaBall` | $\mathsf{Grid}_s[\text{beta Ball}]$ | Lacko–Harman radial family; shape=0 is concentrated on the p-sphere | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L223) | — |
| `Occil.Multivariate.box` | $\mathsf{Grid}_s[\mathrm{box}]$ | Independent coordinatewise grid intervals | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L101) | — |
| `Occil.Multivariate.circle` | $\mathsf{Grid}_s[\mathrm{circle}]$ | Sine and cosine of a uniform angle | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L131) | — |
| `Occil.Multivariate.cone` | $\mathsf{Grid}_s[\mathrm{cone}]$ | Three-dimensional cone whose tip is at z=0 and base at z=height | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L113) | — |
| `Occil.Multivariate.cylinder` | $\mathsf{Grid}_s[\mathrm{cylinder}]$ | Disk point and independent axial coordinate | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L125) | — |
| `Occil.Multivariate.cylinderSurface` | $\mathsf{Grid}_s[\text{cylinder Surface}]$ | Lateral surface of a cylinder, excluding its two end caps | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L139) | — |
| `Occil.Multivariate.ellipsoidSurface` | $\mathsf{Grid}_s[\text{ellipsoid Surface}]$ | Uniform ellipsoid surface via sphere proposals and the surface-area Jacobian | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L203) | — |
| `Occil.Multivariate.exponentialPower` | $\mathsf{Grid}_s[\text{exponential Power}]$ | Generalized normal coordinate used by the source's p-sphere construction | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L33) | — |
| `Occil.Multivariate.halfBall` | $\mathsf{Grid}_s[\text{half Ball}]$ | Reflect one ball coordinate positive | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L156) | — |
| `Occil.Multivariate.halfShell` | $\mathsf{Grid}_s[\text{half Shell}]$ | Reflect one shell coordinate positive | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L160) | — |
| `Occil.Multivariate.halfSphere` | $\mathsf{Grid}_s[\text{half Sphere}]$ | Reflect one sphere coordinate positive | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L152) | — |
| `Occil.Multivariate.hypercube` | $\mathsf{Grid}_s[\mathrm{hypercube}]$ | Repeat independent equal-range grid draws | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L107) | — |
| `Occil.Multivariate.latitudeLongitude` | $\mathsf{Grid}_s[\text{latitude Longitude}]$ | Latitude/longitude in radians; latitude is asin(U), U uniform on (-1,1) | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L165) | — |
| `Occil.Multivariate.shell` | $\mathsf{Grid}_s[\mathrm{shell}]$ | Interpolate radial volume between sphere bounds | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L92) | — |
| `Occil.Multivariate.simplex` | $\mathsf{Grid}_s[\mathrm{simplex}]$ | Uniform barycentric point in the simplex spanned by the supplied vertices | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L175) | — |
| `Occil.Multivariate.sphere` | $\mathsf{Grid}_s[\mathrm{sphere}]$ | Source normalized-EPD construction; p=0 selects its infinity-norm case | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L47) | — |
| `Occil.Multivariate.triangle` | $\mathsf{Grid}_s[\mathrm{triangle}]$ | Fast triangle construction using max(U,V), as in the source article | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L190) | — |
| `Occil.Multivariate.uniformRange` | $\mathsf{Grid}_s[\text{uniform Range}]$ | Affine rescaling of a grid uniform | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L10) | — |
## Numerical multivariate algorithms / Linear

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.binormal` | $\mathsf{Grid}_s[\mathrm{binormal}]$ | Bivariate normal with supplied means, standard deviations and correlation | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L102) | — |
| `Occil.Multivariate.dirichlet` | $\mathsf{Grid}_s[\mathrm{dirichlet}]$ | Gamma-normalization Dirichlet sampler; shape parameters are fixed-point | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L128) | — |
| `Occil.Multivariate.logNormal` | $\mathsf{Grid}_s[\text{log Normal}]$ | Exponentiate correlated normal coordinates | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L144) | — |
| `Occil.Multivariate.meanMixture` | $\mathsf{Grid}_s[\text{mean Mixture}]$ | Normal mean mixture with an independent nonnegative mixing sampler | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L149) | — |
| `Occil.Multivariate.meanVarianceMixture` | $\mathsf{Grid}_s[\text{mean Variance Mixture}]$ | Normal mean/variance mixture, using one shared independent mixing variate | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L155) | — |
| `Occil.Multivariate.normal` | $\mathsf{Grid}_s[\mathrm{normal}]$ | Cholesky transform of independent normal coordinates | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L96) | — |
| `Occil.Multivariate.standardNormals` | $\mathsf{Grid}_s[\text{standard Normals}]$ | Repeat independent scalar normal draws | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L86) | — |
| `Occil.Multivariate.uniformPartition` | $\mathsf{Grid}_s[\text{uniform Partition}]$ | Dirichlet proportions with final-coordinate residual | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L134) | — |
## Numerical multivariate algorithms / PhaseType

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.inhomogeneousMultivariatePhaseType` | $\mathsf{Grid}_s[\text{inhomogeneous Multivariate Phase Type}]$ | Transform multivariate phase-type coordinates | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L104) | — |
| `Occil.Multivariate.inhomogeneousPhaseType` | $\mathsf{Grid}_s[\text{inhomogeneous Phase Type}]$ | Transform a phase-type absorption time | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L59) | — |
| `Occil.Multivariate.initialPhase` | $\mathrm{Cat}(\alpha_1,\ldots,\alpha_n,s-\sum_i\alpha_i)$ | Initial subprobability vector, with the residual assigned to immediate absorption | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L40) | — |
| `Occil.Multivariate.multivariateExponentialPower` | $\mathsf{Grid}_s[\text{multivariate Exponential Power}]$ | Independent radius and normalized Gaussian direction | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L124) | — |
| `Occil.Multivariate.multivariateLinnik` | $\mathsf{Grid}_s[\text{multivariate Linnik}]$ | Normal variance mixture with geometric-stable mixing | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L108) | — |
| `Occil.Multivariate.multivariateLinnikSource` | $\mathsf{Grid}_s[\text{multivariate Linnik Source}]$ | Scale normal vector by geometric-stable mixer | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L118) | — |
| `Occil.Multivariate.multivariatePhaseType` | $\mathsf{Grid}_s[\text{multivariate Phase Type}]$ | Accumulate phase-specific vector rewards | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L65) | — |
| `Occil.Multivariate.phaseType` | $\mathsf{Grid}_s[\text{phase Type}]$ | Accumulate holding times until absorption | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L47) | — |
| `Occil.Multivariate.phaseTypeRandomRewards` | $\mathsf{Grid}_s[\text{phase Type Random Rewards}]$ | Route holding times to sampled reward coordinates | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L89) | — |
## Numerical multivariate algorithms / Stable

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.generalGeometricStable` | $\mathsf{Grid}_s[\text{general Geometric Stable}]$ | General geometric-stable law defined by exponential mixing in the S1 parameterization | [Stable.lean](code/Samplers/Multivariate/Stable.lean#L75) | — |
| `Occil.Multivariate.geometricStable` | $\mathsf{Grid}_s[\text{geometric Stable}]$ | Strictly geometric-stable sampler | [Stable.lean](code/Samplers/Multivariate/Stable.lean#L47) | — |
| `Occil.Multivariate.linnik` | $\mathsf{Grid}_s[\mathrm{linnik}]$ | Symmetric geometric-stable specialization | [Stable.lean](code/Samplers/Multivariate/Stable.lean#L65) | — |
| `Occil.Multivariate.mittagLeffler` | $\mathsf{Grid}_s[\text{mittag Leffler}]$ | Positive geometric-stable specialization | [Stable.lean](code/Samplers/Multivariate/Stable.lean#L68) | — |
| `Occil.Multivariate.stable` | $\mathsf{Grid}_s[\mathrm{stable}]$ | Standard alpha-stable S1 variate | [Stable.lean](code/Samplers/Multivariate/Stable.lean#L11) | — |
| `Occil.Multivariate.vonMises` | $\mathsf{Grid}_s[\text{von Mises}]$ | Best–Fisher von Mises rejection | [Stable.lean](code/Samplers/Multivariate/Stable.lean#L95) | — |
## Rejection

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.rejection` | $\mu(\cdot\mid A)$ | Repeat proposals until accepted | [Rejection.lean](code/Samplers/Continuous/Rejection.lean#L11) | [**verified**](SampLib/Samplers/Rejection.lean) |
## Uniform primitives

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.fairCoin` | $\mathrm{Bern}\!\left(\frac12\right)$ | Test a uniform random bit | [Uniform.lean](code/Samplers/Uniform.lean#L57) | [**verified**](SampLib/Samplers/FairCoin.lean) |
| `Occil.fastDiceRoller` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Lumbroso interval recycling | [Uniform.lean](code/Samplers/Uniform.lean#L26) | [**verified**](SampLib/Samplers/FastDiceRoller.lean) |
| `Occil.rationalCoin` | $\mathrm{Bern}\!\left(a/b\right)$ | Compare a uniform integer rank | [Uniform.lean](code/Samplers/Uniform.lean#L60) | [**verified**](SampLib/Samplers/RationalCoin.lean) |
| `Occil.realCoin` | $\mathrm{Bern}\!\left(p\right)$ | Threshold a continuous uniform | [Uniform.lean](code/Samplers/Uniform.lean#L67) | [**verified**](SampLib/Samplers/RealCoin.lean) |
| `Occil.rndInt` | $\mathrm{Unif}\{0,\ldots,h\}$ | Inclusive bounded integer draw | [Uniform.lean](code/Samplers/Uniform.lean#L16) | [**verified**](SampLib/Samplers/RndInt.lean) |
| `Occil.rndIntExcRange` | $\mathrm{Unif}\{\ell,\ldots,h-1\}$ | Shift a half-open uniform rank | [Uniform.lean](code/Samplers/Uniform.lean#L22) | [**verified**](SampLib/Samplers/RndIntExcRange.lean) |
| `Occil.rndIntRange` | $\mathrm{Unif}\{\ell,\ldots,h\}$ | Shift an inclusive uniform rank | [Uniform.lean](code/Samplers/Uniform.lean#L19) | [**verified**](SampLib/Samplers/RndIntRange.lean) |
| `Occil.uniformFromModulus` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Recursive source-modulus expansion | [Uniform.lean](code/Samplers/Uniform.lean#L39) | [**verified**](SampLib/Samplers/UniformFromModulus.lean) |
| `Occil.uniformInt` | $\mathrm{Unif}\{0,\ldots,n-1\}$ | Primitive bounded integer draw | [Uniform.lean](code/Samplers/Uniform.lean#L12) | [**verified**](SampLib/Samplers/UniformInt.lean) |

## Deterministic generators and helpers

### Bernoulli factories / Arithmetic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.FactoryExtra.addFraction` | Deterministic | Compose callback and auxiliary coin trials | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L38) | — |
| `Occil.FactoryExtra.choose` | Deterministic | Integer binomial coefficient, with zero outside 0 <= k <= n | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L15) | — |
| `Occil.FactoryExtra.divideFraction` | Deterministic | Compose callback and auxiliary coin trials | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L49) | — |
| `Occil.FactoryExtra.fraction` | Deterministic | Canonical rational pair, used to keep adaptive envelope arithmetic small | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L27) | — |
| `Occil.FactoryExtra.intPower` | Deterministic | Compose callback and auxiliary coin trials | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L22) | — |
| `Occil.FactoryExtra.multiplyFraction` | Deterministic | Compose callback and auxiliary coin trials | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L46) | — |
| `Occil.FactoryExtra.subtractFraction` | Deterministic | Compose callback and auxiliary coin trials | [Arithmetic.lean](code/Samplers/Bernoulli/Arithmetic.lean#L42) | — |
### Combinatorial sampling / Basic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.fillArray` | Deterministic | Transform supplied component samples | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L37) | — |
| `Occil.intRange` | Deterministic | The increasing integer list [lo,hi) | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L82) | — |
| `Occil.readArray` | Deterministic | Transform supplied component samples | [Basic.lean](code/Samplers/Combinatorial/Basic.lean#L41) | — |
### Constant coins / Algebraic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.integerSign` | Deterministic | Exact rational-bound or series coin | [Algebraic.lean](code/Samplers/Constants/Algebraic.lean#L15) | — |
### Constant coins / Exponential

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.eBounds` | Deterministic | e in (lower/denominator,upper/denominator), via its factorial series | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L16) | — |
| `Occil.Constants.expMinusBounds` | Deterministic | Exact alternating Taylor bounds for exp(-x/y), x>=0,y>0 | [Exponential.lean](code/Samplers/Constants/Exponential.lean#L103) | — |
### Constant coins / Pi

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Constants.arctanReciprocalBounds` | Deterministic | Exact alternating-series enclosure of arctan(1/q), q>=2, after n>=1 terms | [Pi.lean](code/Samplers/Constants/Pi.lean#L16) | — |
| `Occil.Constants.piBounds` | Deterministic | Exact Machin enclosure pi=16 atan(1/5)-4 atan(1/239) | [Pi.lean](code/Samplers/Constants/Pi.lean#L34) | — |
### Discrete distributions / Combinatorics

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.choose` | Deterministic | Binomial coefficient, with zero outside 0 <= k <= n | [Combinatorics.lean](code/Samplers/Discrete/Combinatorics.lean#L26) | — |
| `Occil.DiscreteExtra.incrementCounter` | Deterministic | Increment one element in an integer list | [Combinatorics.lean](code/Samplers/Discrete/Combinatorics.lean#L48) | — |
| `Occil.DiscreteExtra.integerPower` | Deterministic | Integer power, with a nonnegative exponent | [Combinatorics.lean](code/Samplers/Discrete/Combinatorics.lean#L18) | — |
| `Occil.DiscreteExtra.integerSqrt` | Deterministic | Floor square root of a nonnegative integer, using Newton iteration | [Combinatorics.lean](code/Samplers/Discrete/Combinatorics.lean#L35) | — |
| `Occil.DiscreteExtra.zeroCounters` | Deterministic | A list of n zero counters | [Combinatorics.lean](code/Samplers/Discrete/Combinatorics.lean#L44) | — |
### Discrete distributions / Urns

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.DiscreteExtra.adjustCounter` | Deterministic | Change one integer counter by an integer delta | [Urns.lean](code/Samplers/Discrete/Urns.lean#L60) | — |
| `Occil.DiscreteExtra.urnWeights` | Deterministic | Products of corresponding count and odds entries | [Urns.lean](code/Samplers/Discrete/Urns.lean#L75) | — |
| `Occil.DiscreteExtra.validUrn` | Deterministic | Validate equally sized nonnegative counts and strictly positive integer odds | [Urns.lean](code/Samplers/Discrete/Urns.lean#L67) | — |
### General sampling / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.append` | Deterministic | Transform supplied component samples | [Core.lean](code/Samplers/General/Core.lean#L19) | — |
| `Occil.General.applyMaps` | Deterministic | Apply a chronological list of already sampled maps to one initial state | [Core.lean](code/Samplers/General/Core.lean#L227) | — |
| `Occil.General.tail` | Deterministic | Transform supplied component samples | [Core.lean](code/Samplers/General/Core.lean#L29) | — |
### General sampling / DataModels

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.dataBounds` | Deterministic | Transform supplied component samples | [DataModels.lean](code/Samplers/General/DataModels.lean#L139) | — |
| `Occil.General.denormalizeDataPoint` | Deterministic | Transform supplied component samples | [DataModels.lean](code/Samplers/General/DataModels.lean#L163) | — |
| `Occil.General.normalizeDataPoint` | Deterministic | Transform supplied component samples | [DataModels.lean](code/Samplers/General/DataModels.lean#L152) | — |
| `Occil.General.splitAt` | Deterministic | Split a list at an exact nonnegative position, returning (prefix,suffix) | [DataModels.lean](code/Samplers/General/DataModels.lean#L29) | — |
### General sampling / Points

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.bakersMap` | Deterministic | Baker's tent map, 2*min(x,1-x), on the fixed grid | [Points.lean](code/Samplers/General/Points.lean#L66) | — |
| `Occil.General.bitXor` | Deterministic | Bitwise exclusive-or for nonnegative integers, expressed with arithmetic | [Points.lean](code/Samplers/General/Points.lean#L98) | — |
| `Occil.General.generalizedGoldenRatio` | Deterministic | Root of phi^(dimension+1)=phi+1, found numerically on [1,2] | [Points.lean](code/Samplers/General/Points.lean#L72) | — |
| `Occil.General.halton` | Deterministic | A Halton point; bases should be distinct primes for the usual discrepancy properties | [Points.lean](code/Samplers/General/Points.lean#L38) | — |
| `Occil.General.integerPower` | Deterministic | Transform supplied component samples | [Points.lean](code/Samplers/General/Points.lean#L15) | — |
| `Occil.General.latticePoint` | Deterministic | The concrete MLCG lattice example in Occil's point-selection section | [Points.lean](code/Samplers/General/Points.lean#L193) | — |
| `Occil.General.lfsrPoint` | Deterministic | Consecutive LFSR states as a numerical point | [Points.lean](code/Samplers/General/Points.lean#L213) | — |
| `Occil.General.lfsrStep` | Deterministic | A binary right-shifting LFSR step | [Points.lean](code/Samplers/General/Points.lean#L203) | — |
| `Occil.General.nearestSquaredDistance` | Deterministic | Minimum squared Euclidean distance to a nonempty list of points | [Points.lean](code/Samplers/General/Points.lean#L242) | — |
| `Occil.General.robertsPoint` | Deterministic | Roberts R_d sequence, with seed 1/2 and alpha_j=phi^(-j) | [Points.lean](code/Samplers/General/Points.lean#L87) | — |
| `Occil.General.scrambledRadicalInverse` | Deterministic | Fixed-length digit scrambling of a radical inverse | [Points.lean](code/Samplers/General/Points.lean#L44) | — |
| `Occil.General.shiftPoint` | Deterministic | A shared random shift may randomize an entire low-discrepancy point set | [Points.lean](code/Samplers/General/Points.lean#L57) | — |
| `Occil.General.sobol2` | Deterministic | Transform supplied component samples | [Points.lean](code/Samplers/General/Points.lean#L132) | — |
| `Occil.General.sobolCoordinate` | Deterministic | A Sobol coordinate in Gray-code order from its finite direction-number row | [Points.lean](code/Samplers/General/Points.lean#L110) | — |
| `Occil.General.sobolPoint` | Deterministic | Transform supplied component samples | [Points.lean](code/Samplers/General/Points.lean#L125) | — |
| `Occil.General.squaredDistance` | Deterministic | Transform supplied component samples | [Points.lean](code/Samplers/General/Points.lean#L232) | — |
| `Occil.General.vanDerCorput` | Deterministic | Transform supplied component samples | [Points.lean](code/Samplers/General/Points.lean#L30) | — |
| `Occil.General.vanDerCorputRational` | Deterministic | Base-b radical inverse as an exact numerator/denominator pair | [Points.lean](code/Samplers/General/Points.lean#L22) | — |
### Integer and weighted sampling / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.integerPower` | Deterministic | Integer powers, including x^0=1; negative exponents are rejected | [Core.lean](code/Samplers/Weighted/Core.lean#L24) | — |
| `Occil.Weighted.powerOfTwoCeiling` | Deterministic | Smallest power of two at least n, for n>0 | [Core.lean](code/Samplers/Weighted/Core.lean#L32) | — |
| `Occil.Weighted.validWeights` | Deterministic | Nonnegative integer weights with a strictly positive sum | [Core.lean](code/Samplers/Weighted/Core.lean#L16) | — |
| `Occil.WeightedVariants.bitLength` | Deterministic | Positive integer bit length; bitLength(0)=0 | [Core.lean](code/Samplers/Weighted/Core.lean#L49) | — |
### Integer and weighted sampling / Dynamic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.lowBit` | Deterministic | The least significant set-bit value of a positive integer | [Dynamic.lean](code/Samplers/Weighted/Dynamic.lean#L17) | — |
### Integer and weighted sampling / Reductions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.roundBinary` | Deterministic | Integer-weight sampling construction | [Reductions.lean](code/Samplers/Weighted/Reductions.lean#L50) | — |
### Integer and weighted sampling / Reservoir

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.insertProbability` | Deterministic | Insert a (probability numerator,label) pair into ascending probability order | [Reservoir.lean](code/Samplers/Weighted/Reservoir.lean#L33) | — |
### Integer and weighted sampling / Tables

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.cumulativeTable` | Deterministic | Prefix sums, with validation; returns (total,cumulative list) | [Tables.lean](code/Samplers/Weighted/Tables.lean#L17) | — |
| `Occil.Weighted.rationalWeights` | Deterministic | Normalize rational weights (numerator,positive denominator) to integers | [Tables.lean](code/Samplers/Weighted/Tables.lean#L48) | — |
### List operations

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.getAt` | Deterministic | Transform supplied component samples | [Data.lean](code/Samplers/Data.lean#L23) | — |
| `Occil.insertReal` | Deterministic | Transform supplied component samples | [Data.lean](code/Samplers/Data.lean#L39) | — |
| `Occil.length` | Deterministic | Transform supplied component samples | [Data.lean](code/Samplers/Data.lean#L11) | — |
| `Occil.removeAt` | Deterministic | Returns (selected item, remaining list) | [Data.lean](code/Samplers/Data.lean#L30) | — |
| `Occil.sumInts` | Deterministic | Transform supplied component samples | [Data.lean](code/Samplers/Data.lean#L17) | — |
### Numerical arithmetic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numeric.abs` | Deterministic | Integer absolute value, without fixed-point rescaling | [Numeric.lean](code/Samplers/Numeric.lean#L23) | — |
| `Occil.Numeric.atan` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L190) | — |
| `Occil.Numeric.atanRaw` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L179) | — |
| `Occil.Numeric.atanSeries` | Deterministic | Arctangent's power series, used only on arguments of magnitude <=1/2 | [Numeric.lean](code/Samplers/Numeric.lean#L170) | — |
| `Occil.Numeric.cos` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L155) | — |
| `Occil.Numeric.cosRaw` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L140) | — |
| `Occil.Numeric.div` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L35) | — |
| `Occil.Numeric.exp` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L84) | — |
| `Occil.Numeric.expRaw` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L68) | — |
| `Occil.Numeric.log` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L107) | — |
| `Occil.Numeric.logRaw` | Deterministic | Log at working precision: normalize to [1,2), then use log(z)=2*(y+y^3/3+...), y=(z-1)/(z+1) | [Numeric.lean](code/Samplers/Numeric.lean#L91) | — |
| `Occil.Numeric.logTwo` | Deterministic | Natural logarithm of 2 rounded down onto the requested grid | [Numeric.lean](code/Samplers/Numeric.lean#L49) | — |
| `Occil.Numeric.mul` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L32) | — |
| `Occil.Numeric.normalCDF` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L217) | — |
| `Occil.Numeric.normalCDFRaw` | Deterministic | Standard normal CDF at working precision, using a five-term tail fit | [Numeric.lean](code/Samplers/Numeric.lean#L197) | — |
| `Occil.Numeric.normalQuantile` | Deterministic | Quantile of the approximate standard normal CDF, by bracketed bisection | [Numeric.lean](code/Samplers/Numeric.lean#L224) | — |
| `Occil.Numeric.pi` | Deterministic | Pi rounded down onto the requested grid | [Numeric.lean](code/Samplers/Numeric.lean#L42) | — |
| `Occil.Numeric.pow` | Deterministic | Real exponentiation for nonnegative bases | [Numeric.lean](code/Samplers/Numeric.lean#L114) | — |
| `Occil.Numeric.quotient` | Deterministic | Signed quotient rounded toward zero; the divisor must be positive | [Numeric.lean](code/Samplers/Numeric.lean#L27) | — |
| `Occil.Numeric.reduceAngle` | Deterministic | Reduce an angle to [-pi,pi) at the working scale | [Numeric.lean](code/Samplers/Numeric.lean#L125) | — |
| `Occil.Numeric.sin` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L150) | — |
| `Occil.Numeric.sinRaw` | Deterministic | Transform supplied component samples | [Numeric.lean](code/Samplers/Numeric.lean#L130) | — |
| `Occil.Numeric.sqrt` | Deterministic | Floor of sqrt(scale*x), hence a Q(scale) square root within one grid unit | [Numeric.lean](code/Samplers/Numeric.lean#L56) | — |
| `Occil.Numeric.tan` | Deterministic | Tangent; rejects arguments whose rounded cosine is zero | [Numeric.lean](code/Samplers/Numeric.lean#L161) | — |
### Numerical grid algorithms / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Numerical.positiveGrid` | Deterministic | Clamp to the first positive cell | [Core.lean](code/Samplers/Numerical/Core.lean#L18) | — |
### Numerical grid algorithms / SpecialDistributions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Specialized.integerPower` | Deterministic | Integer exponent, used for the exact-grid discrete-Laplace CDF | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L63) | — |
| `Occil.Specialized.tulapCDF` | Deterministic | CDF of G1-G2+Uniform(-1/2,1/2), with P(G=k)=(1-b)b^k | [SpecialDistributions.lean](code/Samplers/Numerical/SpecialDistributions.lean#L71) | — |
### Numerical multivariate algorithms / Copulas

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.studentCDF` | Deterministic | Midpoint quadrature for the Student CDF, using the cosine-integral identity | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L91) | — |
### Numerical multivariate algorithms / Geometry

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.pNorm` | Deterministic | Transform supplied component samples | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L14) | — |
| `Occil.Multivariate.positiveCoordinate` | Deterministic | Reflect a selected coordinate into the positive half-space | [Geometry.lean](code/Samplers/Multivariate/Geometry.lean#L146) | — |
### Numerical multivariate algorithms / Linear

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.add` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L25) | — |
| `Occil.Multivariate.cholesky` | Deterministic | Lower-triangular Cholesky factor | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L57) | — |
| `Occil.Multivariate.constants` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L21) | — |
| `Occil.Multivariate.covarianceTransform` | Deterministic | Transform independent coordinates by mu + chol(covariance)*coordinates | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L90) | — |
| `Occil.Multivariate.dot` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L34) | — |
| `Occil.Multivariate.integerSquares` | Deterministic | Sum of raw integer coordinate squares, without fixed-point truncation | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L41) | — |
| `Occil.Multivariate.matrixVector` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L52) | — |
| `Occil.Multivariate.norm` | Deterministic | Euclidean norm in the coordinate grid, delaying rounding until after sqrt | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L49) | — |
| `Occil.Multivariate.normalize` | Deterministic | Rounding-preserving normalization: the last coordinate receives the residual | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L113) | — |
| `Occil.Multivariate.scaleVector` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L31) | — |
| `Occil.Multivariate.squaredNorm` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L45) | — |
| `Occil.Multivariate.zeros` | Deterministic | Transform supplied component samples | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L17) | — |
### Numerical multivariate algorithms / PhaseType

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.addAt` | Deterministic | Transform supplied component samples | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L81) | — |
| `Occil.Multivariate.append` | Deterministic | Transform supplied component samples | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L11) | — |
| `Occil.Multivariate.generatorTransitions` | Deterministic | Convert each subgenerator row into integer transition weights, appending absorption | [PhaseType.lean](code/Samplers/Multivariate/PhaseType.lean#L18) | — |

## Stateful and sampling support

### Continuous distributions

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.decreasingTrial` | Support operation | Number of strict decreases below x | [Continuous.lean](code/Samplers/Continuous.lean#L15) | — |
| `Occil.gaussianSelector` | Support operation | Transform supplied component samples | [Continuous.lean](code/Samplers/Continuous.lean#L87) | — |
| `Occil.gaussianSelectorC` | Support operation | Transform supplied component samples | [Continuous.lean](code/Samplers/Continuous.lean#L78) | — |
| `Occil.gaussianSelectorCoin` | Support operation | Transform supplied component samples | [Continuous.lean](code/Samplers/Continuous.lean#L81) | — |
### General sampling / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.fold` | Support operation | Apply supplied callbacks to structured values | [Core.lean](code/Samplers/General/Core.lean#L32) | — |
| `Occil.General.map` | Support operation | Apply supplied callbacks to structured values | [Core.lean](code/Samplers/General/Core.lean#L24) | [proof](SampLib/Samplers/ListMapSampling.lean) |
| `Occil.General.sliceStep` | $K_{\mathrm{slice}}(x,\cdot)$ | Sample height, then reject within slice | [Core.lean](code/Samplers/General/Core.lean#L297) | [proof](SampLib/Samplers/SliceStep.lean) |
### General sampling / DataModels

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.General.vectorZipWith` | Support operation | Apply supplied callbacks to structured values | [DataModels.lean](code/Samplers/General/DataModels.lean#L133) | — |
### Integer and weighted sampling / Aliases

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.voseTable` | Support operation | Vose alias preprocessing with explicit small/large stacks | [Aliases.lean](code/Samplers/Weighted/Aliases.lean#L17) | — |
### Integer and weighted sampling / Dynamic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.fenwickSet` | Support operation | Replace one weight and update every affected cumulative-tree node | [Dynamic.lean](code/Samplers/Weighted/Dynamic.lean#L49) | — |
| `Occil.WeightedVariants.newFenwick` | Support operation | Mutable cumulative weights in a Fenwick tree | [Dynamic.lean](code/Samplers/Weighted/Dynamic.lean#L28) | — |
### Integer and weighted sampling / Optimal

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.WeightedVariants.optimalMatrix` | Support operation | Integer-weight sampling construction | [Optimal.lean](code/Samplers/Weighted/Optimal.lean#L17) | — |
### Integer and weighted sampling / Trees

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.matrixColumn` | Support operation | Scan a binary probability column | [Trees.lean](code/Samplers/Weighted/Trees.lean#L17) | — |
### Integer and weighted sampling / Uniform

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Weighted.newRecycler` | Support operation | A reusable uniform entropy pool, storing (value,number of possible values) | [Uniform.lean](code/Samplers/Weighted/Uniform.lean#L49) | — |
### Lazy coin factories

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.newUniformBag` | Support operation | A lazy node is unsampled nil, or cons(bit,next node) | [Lazy.lean](code/Samplers/Lazy.lean#L13) | — |
| `Occil.uniformBagLess` | Support operation | Compare the represented U with a rational x/y, with exact integer arithmetic | [Lazy.lean](code/Samplers/Lazy.lean#L40) | — |
| `Occil.uniformBagPrefix` | Support operation | First n bits as an integer in [0,2^n); rereading the same prefix is stable | [Lazy.lean](code/Samplers/Lazy.lean#L28) | — |
| `Occil.uniformBagStep` | Support operation | Read and cache one bit and the remaining stream | [Lazy.lean](code/Samplers/Lazy.lean#L16) | — |
### Lazy exact reals / Arithmetic

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.add` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L22) | — |
| `Occil.PSRN.divide` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L74) | — |
| `Occil.PSRN.integerPowerReal` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L77) | — |
| `Occil.PSRN.maximum` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L117) | — |
| `Occil.PSRN.minimum` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L114) | — |
| `Occil.PSRN.multiply` | Support operation | Interval multiplication also works when the operands share latent digits | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L46) | — |
| `Occil.PSRN.negate` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L16) | — |
| `Occil.PSRN.powerRational` | Support operation | Rational powers of a positive lazy real, including negative exponents | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L106) | — |
| `Occil.PSRN.reciprocal` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L61) | — |
| `Occil.PSRN.root` | Support operation | Positive n-th root by rational bisection; no numerical transcendental primitive is used | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L87) | — |
| `Occil.PSRN.scaleRational` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L35) | — |
| `Occil.PSRN.subtract` | Support operation | Transform supplied component samples | [Arithmetic.lean](code/Samplers/PSRN/Arithmetic.lean#L32) | — |
### Lazy exact reals / Core

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.fillGeometricBag` | Support operation | FillGeometricBag in the binary prefix-stream representation | [Core.lean](code/Samplers/PSRN/Core.lean#L89) | — |
| `Occil.PSRN.fillUniformBag` | Support operation | Reveal the first n cached bits of a uniform bag; returns the original bag | [Core.lean](code/Samplers/PSRN/Core.lean#L47) | — |
| `Occil.PSRN.floorScaled` | Support operation | Refine until floor(scale*x) is unambiguous | [Core.lean](code/Samplers/PSRN/Core.lean#L65) | — |
| `Occil.PSRN.fromUniformBag` | Support operation | Transform supplied component samples | [Core.lean](code/Samplers/PSRN/Core.lean#L36) | — |
| `Occil.PSRN.integerPower` | Support operation | Exact integer power for a nonnegative exponent | [Core.lean](code/Samplers/PSRN/Core.lean#L25) | — |
| `Occil.PSRN.less` | Support operation | Exact comparison of independent or shared oracle values whenever separated | [Core.lean](code/Samplers/PSRN/Core.lean#L51) | — |
| `Occil.PSRN.rational` | Support operation | Transform supplied component samples | [Core.lean](code/Samplers/PSRN/Core.lean#L31) | — |
| `Occil.PSRN.rounded` | Support operation | Transform supplied component samples | [Core.lean](code/Samplers/PSRN/Core.lean#L76) | — |
| `Occil.PSRN.uniformLess` | Support operation | Compare two lazy uniforms directly, sharing their memoized digits | [Core.lean](code/Samplers/PSRN/Core.lean#L81) | — |
### Lazy exact reals / Gaussian

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.gaussianSelector` | Support operation | Karney's Gaussian selector, with all comparisons performed on lazy reals | [Gaussian.lean](code/Samplers/PSRN/Gaussian.lean#L17) | — |
### Lazy exact reals / Geometry

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.PSRN.divideCoordinates` | Support operation | Transform supplied component samples | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L23) | — |
| `Occil.PSRN.multiplyCoordinates` | Support operation | Transform supplied component samples | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L28) | — |
| `Occil.PSRN.normSquared` | Support operation | Squared Euclidean norm of a list of lazy coordinates | [Geometry.lean](code/Samplers/PSRN/Geometry.lean#L18) | — |
### List operations

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.repeatSample` | Support operation | Build a list of n independent calls to a unit-taking sampler | [Data.lean](code/Samplers/Data.lean#L48) | [proof](SampLib/Samplers/SampleWithReplacement.lean) |
### Numerical multivariate algorithms / Copulas

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.transformMarginals` | Support operation | Apply supplied callbacks to structured values | [Copulas.lean](code/Samplers/Multivariate/Copulas.lean#L37) | — |
### Numerical multivariate algorithms / Linear

| Sampler | Law | Method | Code | Proof |
| --- | --- | --- | --- | --- |
| `Occil.Multivariate.map` | Support operation | Apply supplied callbacks to structured values | [Linear.lean](code/Samplers/Multivariate/Linear.lean#L12) | — |

---

Generated by `python3 agent-scripts/law_index.py` from [the law catalog](agent-docs/SamplerLaws.json), implementation declarations, and accepted review records. GitHub renders the inline math with MathJax.
