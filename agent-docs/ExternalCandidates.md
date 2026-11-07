# External sampler candidates

This document lists samplers from freely available books and papers that the repository does not yet implement. It targets exact algorithms that the project can verify. Every algorithm statement, section number, page number, and constant below comes from a reading of the source itself.

## How the candidates were chosen

The search covered Luc Devroye's "Non-Uniform Random Variate Generation" (1986), Flajolet, Pelletier, and Soria ("On Buffon machines and numbers"), Morina, Łatuszyński, Nayar, and Wendland (the dice enterprise paper), Devroye and Gravel (arXiv 1502.02539), and Canonne, Kamath, and Steinke (arXiv 2004.00010). Each candidate had to meet three tests:

- The algorithm is exact, so no floating-point approximation changes the target law. Where an algorithm is exact only over a lazy real number model, the entry says so.
- It needs only uniform integers or bits, integer or rational arithmetic, comparisons of lazy uniforms against exactly computable reals, or callbacks to coins and samplers.
- The repository has no equivalent sampler. The check searched `LAWS.md`, `code/README.md`, and a name search of `code/Samplers`.

Page numbers for Devroye are the printed page numbers of the book. Page numbers for arXiv papers are the page numbers of the arXiv PDF. The repository already covers most exact Bernoulli factory, constant coin, lazy real, weighted choice, and Karney-style Gaussian material, so the gaps cluster in combinatorial objects, sequential sampling, series-based continuous laws, and a few coin-driven discrete laws.

## Summary table

The following table lists every candidate. The status column reads "Missing" when the repository has no equivalent and "Partial" when a related sampler exists but this exact form does not. The primitives column uses these codes: UI for uniform integers or bits, Q for integer or rational arithmetic, Big for arbitrary-size integers, LU for exact comparison of a lazy uniform against an exactly enclosed real, and CB for coin or sampler callbacks.

| No. | Algorithm | Source | Target law | Primitives | Exact | Status |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | Prüfer-code labeled trees | Devroye XIII.5.1, pp. 662-663 | Uniform labeled tree on n vertices | UI | Yes | Missing |
| 2 | Sequential balanced parentheses and binary trees | Devroye XIII.3.1 to 3.3, pp. 652-657 | Uniform binary tree with n nodes | UI, Q | Yes | Missing |
| 3 | Set partitions by the Stirling recurrence | Devroye XIII.4.2, p. 660 | Uniform partition of [n] into k blocks | UI, Q, Big | Yes | Missing |
| 4 | Integer partitions by Wilf's recurrence | Devroye XIII.4.3, exercise 2, p. 661 | Uniform integer partition of n | UI, Q, Big | Yes | Missing |
| 5 | Decoding method for permutations | Devroye XIII.1.2, pp. 643-645; XIII.2.1, p. 648 | Uniform permutation from one integer | UI, Big | Yes | Missing |
| 6 | Sparse random graphs by geometric skips | Devroye XIII.6.1, pp. 667-668 | G(n, p) and G(n, e) | UI, CB | Yes | Partial |
| 7 | Sequential sampling by skip inversion | Devroye XII.3.3, p. 624 | Sorted uniform k-subset of [n] | UI or LU, Q | Yes | Missing |
| 8 | Ghost point sampling | Devroye XII.3.5, pp. 626-628 | Sorted uniform k-subset of [n] | UI, lazy Beta | Yes | Missing |
| 9 | Oversampling | Devroye XII.4, p. 636 | Sorted uniform k-subset of [n] | LU, UI | Yes | Missing |
| 10 | Guide table | Devroye III.2.4, pp. 96-98 | Categorical with integer weights | UI, Q | Yes | Missing |
| 11 | Marsaglia multi-level table | Devroye III.3.2, pp. 104-106 | Categorical with base-b weights | UI | Yes | Partial |
| 12 | Binomial by geometric waiting | Devroye X.4, Lemma 4.4, p. 522 | Bin(n, a/b) | CB | Yes | Partial |
| 13 | Forsythe-von Neumann rejection | Devroye IV.2, pp. 121-124 | Density proportional to g(x) exp(-F(x)), F in [0, 1] | LU, CB | Yes | Partial |
| 14 | Alternating series method | Devroye IV.5, pp. 151-154 | Densities with an alternating series ratio | LU, real enclosures | Yes | Missing |
| 15 | Kolmogorov-Smirnov law | Devroye IV.5.6, pp. 161-165 | Limit law of the Kolmogorov statistic | LU, real enclosures | Yes | Missing |
| 16 | Jöhnk Beta generator | Devroye IX.3, p. 418 | Beta(a, b), a and b positive | LU, lazy powers | Yes | Missing |
| 17 | Bit-model rejection with interval oracles | Devroye and Gravel, sections 3.6 and 3.7 | Absolutely continuous laws to accuracy epsilon | UI, interval oracle | Yes | Partial |
| 18 | Homogeneous Poisson process | Devroye VI.1.2, p. 248 | Poisson process on [0, T] | UI, LU | Yes | Missing |
| 19 | Thinning for Poisson processes | Devroye VI.1, p. 255 | Non-homogeneous Poisson process | LU, CB | Yes | Missing |
| 20 | Discrete Gaussian | Canonne, Kamath, and Steinke, section 5.3 | Discrete Gaussian on Z, rational variance | UI, Q, CB | Yes | Missing |
| 21 | Ladder chain from a coin | Morina et al., section 3.4 | Tilted binomial law from a p-coin | CB, UI | Yes | Missing |
| 22 | Poisson and logarithmic laws from a coin | Flajolet, Pelletier, and Soria, section 2.1 | Poisson(lambda), Logarithmic(lambda) from a lambda-coin | CB, UI | Yes | Missing |
| 23 | Grammar-driven algebraic coins | Flajolet, Pelletier, and Soria, sections 3.1 and 3.2 | Bern((1 - lambda) S(lambda / 2)) for a grammar | CB, UI | Yes | Missing |

## Candidates

Each subsection gives the facts in a fixed order, then the pseudocode. The repository line states the result of the search.

### 1. Prüfer-code labeled trees

The following facts describe the sampler:

- Source: Devroye, section XIII.5.1 (Prüfer's construction, Theorem 5.1, pp. 662-663). Section XIII.5.2 (p. 664) gives Klingsberg's linear-time decoder.
- Target: the uniform distribution on the n^(n-2) labeled trees on the vertices 1 to n, for n at least 2.
- Primitives: n - 2 uniform integers in [1, n]. The decoder needs the smallest current leaf, found with a heap or with Klingsberg's two-pointer scan.
- Exact: yes. Termination is deterministic after n - 2 draws.
- Repository: missing. `randomGraph` covers only G(n, p).

The pseudocode follows:

```
sampleLabeledTree(n):
  a[1..n-2] <- independent uniform integers in [1, n]
  deg[v] <- 1 + number of occurrences of v in a
  for i from 1 to n-2:
    leaf <- smallest v with deg[v] = 1
    emit edge (leaf, a[i]); deg[leaf] <- 0; deg[a[i]] <- deg[a[i]] - 1
  emit the edge between the two vertices that still have degree 1
```

The proof splits into the bijection between codewords and trees, and the fact that a uniform codeword gives a uniform tree.

### 2. Sequential balanced parentheses and binary trees

The following facts describe the sampler:

- Source: Devroye, section XIII.3. Theorem 3.1 (p. 652) maps balanced parenthesis strings of length 2n to binary trees with n nodes, Theorem 3.3 (p. 654) counts them with the Catalan number, and section XIII.3.3 (pp. 656-657) gives the sequential generator of Arnold and Sleep (1980).
- Target: the uniform distribution on binary trees with n nodes, through uniform balanced strings.
- Primitives: one uniform comparison per step against a rational number built from small integers.
- Exact: yes. With a lazy uniform or a uniform integer below the denominator, each comparison is exact. It runs in time linear in n and never rejects.
- Repository: missing.

The pseudocode follows:

```
sampleBalanced(n):
  x <- 0                                  # height of the walk
  for t from 0 to 2n-1:
    u <- uniform in (0, 1)
    if u <= ((x + 2) / (x + 1)) * ((2n - t - x) / (2 * (2n - t))):
      x <- x + 1; emit "("
    else:
      x <- x - 1; emit ")"
```

The opening probability equals the ratio of the numbers of nonnegative completions after an up step and after any step. At height 0 it is 1, and it is 0 when x equals 2n - t, so the walk stays nonnegative and ends at 0. Rebuilding the tree from the string follows the traversal in the proof of Theorem 3.1.

### 3. Set partitions by the Stirling recurrence

The following facts describe the sampler:

- Source: Devroye, section XIII.4.2 (p. 660), the "random partition generator based upon recurrence relation for Stirling numbers". Section XIII.4.1 (pp. 658-659) defines the codeword and the table of Stirling numbers of the second kind. Devroye credits Wilf (1977) and Nijenhuis and Wilf (1978).
- Target: the uniform distribution on the partitions of {1, ..., n} into k nonempty blocks. Draw k first with weight S(n, k) to get a uniform set partition with any number of blocks.
- Primitives: uniform bignum draws or rational comparisons with S(n-1, k-1) / S(n, k), plus a uniform integer in [1, k].
- Exact: yes. Time is O(n) per partition after an O(nk) table.
- Repository: missing. `DiscreteExtra.bell` samples a number, not a partition.

The pseudocode follows:

```
samplePartitionCodeword(n, k):            # blocks ordered by smallest element
  for m from n down to 1:
    if uniform(0,1) <= S(m-1, k-1) / S(m, k):
      X[m] <- k; k <- k - 1                # m opens the block numbered k
    else:
      X[m] <- uniform integer in [1, k]    # m joins an existing block
  return X[1..n]
```

### 4. Integer partitions by Wilf's recurrence

The following facts describe the sampler:

- Source: Devroye, section XIII.4.3, exercise 2 (p. 661). The book states the recurrence p(n, k) = p(n-1, k-1) + p(n-k, k) for partitions of n whose largest part is k, and leaves the algorithm as an exercise. The method is due to Wilf (1977) and Nijenhuis and Wilf (1978).
- Target: the uniform distribution on the partitions of n. Choose the largest part k with weight p(n, k), then run the recurrence.
- Primitives: uniform bignum draws and a table of p(m, j).
- Exact: yes.
- Repository: missing. `uniformPartition` samples Dirichlet proportions, not integer partitions.

The pseudocode follows:

```
samplePartition(n):
  k <- sample from weights p(n, k), k = 1..n
  ops <- []; m <- n
  while m > 0:
    if uniform(0,1) <= p(m-1, k-1) / p(m, k):
      ops.append(UNIT); m <- m - 1; k <- k - 1
    else:
      ops.append(COPY(k)); m <- m - k      # adjoin another copy of the largest part
  parts <- []                              # replay the operations from last to first
  for op in reverse(ops):
    if op = UNIT: raise the largest part of parts by 1 (add a part 1 if parts is empty)
    else:         add a part of size op.k to parts
  return parts
```

A remark on method: Fristedt's multiplicity method needs the real number exp(-pi / sqrt(6n)) and is not exact, so it is left out.

### 5. Decoding method for permutations

The following facts describe the sampler:

- Source: Devroye, section XIII.1.2 (the decoding method, pp. 643-645) with Example 1.1 (Lehmer's factorial code, p. 644), and Robson's one-pass variant in section XIII.2.1 (p. 648).
- Target: the uniform distribution on permutations of [n], from one uniform integer in [1, n!].
- Primitives: one uniform bignum below n! and division with remainder.
- Exact: yes. The book notes that this costs multiple-precision arithmetic once n exceeds about 12.
- Repository: missing. `shuffle` uses n - 1 draws and has no integer-code proof. The decoding gives an independent bijection proof, and the general principle of section XIII.1.2 (decode a uniform integer, with rejection if the code has gaps, p. 645) reaches other objects.

The pseudocode follows:

```
decodePermutation(n):
  x <- uniform integer in [0, n!)
  sigma <- [1, 2, ..., n]
  for i from n down to 2:
    (x, z) <- (x div i, x mod i)           # Robson's form
    swap sigma[i] and sigma[z + 1]
  return sigma
```

### 6. Sparse random graphs by geometric skips

The following facts describe the sampler:

- Source: Devroye, section XIII.6.1 (pp. 667-668). The book notes that waiting times between selected edges are geometric, and codes edges as integers with f(u, v) = (u-1)n - u(u-1)/2 + (v-u).
- Target: G(n, p) with expected O(pn^2) work, and G(n, e) as a uniform subset of e edges.
- Primitives: Geometric(p) draws for rational p, and integer arithmetic for the edge code.
- Exact: yes.
- Repository: partial. `randomGraph` uses independent edge draws, and `code/README.md` says that it does not implement the geometric skip variant.

The pseudocode follows:

```
sparseGraph(n, p):
  idx <- 0; edges <- []
  loop:
    idx <- idx + Geometric1(p)            # next selected edge position
    if idx > C(n, 2): return edges
    edges.append(decodeEdge(idx))
```

### 7. Sequential sampling by skip inversion

The following facts describe the sampler:

- Source: Devroye, section XII.3.3 (p. 624). The skip X to the next selected element of a k-subset of [n] has 1 - F(i) = C(n-i, k) / C(n, k), and (1 - F(i+1)) / (1 - F(i)) = (n - i - k) / (n - i). Sections XII.3.4 and XII.3.5 add the speedups of Devroye and Yuen (1981).
- Target: a uniform sorted k-subset of [n], produced one skip at a time.
- Primitives: a uniform value compared against rational numbers. A lazy uniform makes each comparison exact. The correction step of section XII.3.4 uses a real power and is not exact.
- Exact: yes for the plain inversion. Expected work is (n + 1) / (k + 1) steps per skip.
- Repository: missing. `sampleInOrder` makes one decision per element, which is the algorithm that section XII.3.3 ends with (p. 630).

The pseudocode follows:

```
nextSkip(n, k):                          # k items remain among n
  u <- uniform in (0,1)
  s <- 0; q <- (n - k) / n               # q = Pr(skip > s)
  while u < q:
    s <- s + 1
    q <- q * (n - s - k) / (n - s)
  return s
```

### 8. Ghost point sampling

The following facts describe the sampler:

- Source: Devroye, section XII.3.5 (pp. 626-628), Theorem 3.5, after Devroye and Yuen (1981).
- Target: the same skip law as candidate 7. The skip equals one plus the floor of the minimum of k independent uniform draws on {1, ..., n-k+1}, where draws flagged as ghosts are replaced by a large sentinel.
- Primitives: uniform integers, one rational comparison per ghost test, and one Beta(Size, k - Size + 1) variate. `PSRN.newBeta` supplies integer shapes.
- Exact: yes with an exact Beta. The expected time is bounded uniformly for k at most rho n with rho below 1 (Theorem 3.6, p. 629). It needs O(k) extra memory.
- Repository: missing.

The pseudocode follows:

```
ghostPoint(n, k):
  L <- empty set
  repeat:
    repeat: w <- uniform integer in [1, k] until w not in L
    L.add(w)
  until uniform(0,1) >= (w - 1) / (n - k + w)     # w is not a ghost
  b <- Beta(|L|, k - |L| + 1)
  return floor(1 + b * (n - k + 1))
```

### 9. Oversampling

The following facts describe the sampler:

- Source: Devroye, section XII.4 (p. 636).
- Target: a uniform sorted k-subset of [n].
- Primitives: the order statistics of K1 uniform draws (`PSRN.newOrderStatistic`), integer floors of lazy uniforms, and sequential sampling for the removal step.
- Exact: yes. Rejection happens when fewer than k distinct values remain.
- Repository: missing.

The pseudocode follows:

```
oversample(n, k, K1):
  repeat:
    U <- sorted sample of K1 independent uniforms
    X <- distinct values among floor(1 + n * U[i])
  until |X| >= k
  mark a uniform sorted subset of size |X| - k of X by sequential sampling
  return the unmarked elements
```

The choice of K1 as a function of k and n is the design question that the book discusses.

### 10. Guide table

The following facts describe the sampler:

- Source: Devroye, section III.2.4 (pp. 96-98), after Chen and Asau (1974). Theorem 2.3 bounds the expected number of comparisons by 2, and a table with alpha times (K + 1) entries gives at most 1 + 1/alpha.
- Target: the categorical law with integer weights w_0 to w_K and total W. The book uses real cumulative sums. With integers, every step is exact.
- Primitives: one uniform integer in [0, W) and an index table of size about K.
- Exact: yes.
- Repository: missing. `aliasSamples`, `cumulativeChoice`, and `fenwickDraw` sample the same law with other structures.

The pseudocode follows:

```
build(w):
  C[i] <- w_0 + ... + w_i
  for j from 0 to m-1:  G[j] <- smallest i with C[i] * m > j * W
sample():
  r <- uniform integer in [0, W)
  i <- G[floor(r * m / W)]
  while C[i] <= r: i <- i + 1
  return i
```

For r in group j, the index G[j] never exceeds the answer, so the forward scan returns the smallest i with C[i] above r. The book stores the equivalent guide value g_i, the largest j with q_j below i / (K + 1), and scans backward (p. 97).

### 11. Marsaglia multi-level table

The following facts describe the sampler:

- Source: Devroye, sections III.3.1 and III.3.2 (pp. 102-106), after Marsaglia (1963). The first level reuses one uniform draw to index a short table of blocks, and falls through to a longer table of leftover entries when the block is mixed.
- Target: a categorical law whose probabilities are multiples of 1/M for an integer M, for example 1/1000 or 2^-32.
- Primitives: one uniform integer in [0, M), reused at each level.
- Exact: yes.
- Repository: partial. `knuthYao` and `fastLoadedDiceRoller` implement the base 2 form. The book's version trades table space for a constant number of lookups.

The pseudocode follows:

```
sample():                                # M = M0 * M1, level-1 blocks of size M1
  u <- uniform integer in [0, M)
  b <- B[floor(u / M1)]
  if b is a value: return b              # whole block holds one value
  return A[u]                            # mixed block: read the full table
```

### 12. Binomial by geometric waiting

The following facts describe the sampler:

- Source: Devroye, section X.4, Lemma 4.4 (the first waiting time property, p. 522). The book also gives a coin-flip method with recycling of the uniform draw (p. 524).
- Target: Bin(n, p) for rational p. The result X is the smallest integer with G_1 + ... + G_(X+1) greater than n, for independent Geometric(p) variates G_i supported on {1, 2, ...}.
- Primitives: Geometric(p) draws, which a p-coin supplies.
- Exact: yes. Expected cost is O(np) draws.
- Repository: partial. `binomialBinary`, `binomialHalfBits`, and `binomialHalfRejection` exist. This variant gives a proof through the Bernoulli process.

The pseudocode follows:

```
binomialWaiting(n, p):
  total <- 0; x <- 0
  loop:
    total <- total + Geometric1(p)
    if total > n: return x
    x <- x + 1
```

### 13. Forsythe-von Neumann rejection

The following facts describe the sampler:

- Source: Devroye, section IV.2 (pp. 121-124). Theorem 2.1 (p. 122) shows that a descending chain of uniform draws has odd length with probability exp(-F(x)). Forsythe's method (p. 123) applies it to densities cg(x)exp(-F(x)).
- Target: a density f(x) = c g(x) exp(-F(x)), where g is a sampleable density and F takes values in [0, 1].
- Primitives: a sampler for g and a lazy uniform compared with the real number F(X). The book notes that the expected number of uniform draws lies between 2 and e + e^2.
- Exact: yes, if F(x) is computable to any accuracy.
- Repository: partial. `exponential` and `expMinusFactory` use the chain for exp(-p). The reusable combinator for a generic F is missing.

The pseudocode follows:

```
forsythe(sampleG, F):
  loop:
    x <- sampleG()
    w <- F(x); k <- 1
    loop:
      u <- fresh uniform
      if u > w: break
      w <- u; k <- k + 1
    if k is odd: return x
```

### 14. Alternating series method

The following facts describe the sampler:

- Source: Devroye, section IV.5 (pp. 151-154). Section IV.5.1 gives the general series method with bounds f_n at most f at most g_n (p. 151), and the alternating form (pp. 152-153). Theorem 5.1 (p. 155) gives the expected cost as c times the mean of the sum of the a_i.
- Target: a density f(x) = c h(x) (1 - a_1(x) + a_2(x) - ...), where h is sampleable, c is at least 1, and a_n decreases to 0 in n.
- Primitives: a sampler for h, a lazy uniform, and exact enclosures of the a_n(X).
- Exact: yes. The sums alternate around f, so every partial sum is a valid bound.
- Repository: missing. `pdfRejection` assumes a density that one step computes.

The pseudocode follows:

```
seriesMethod(sampleH, a, c):
  loop:
    x <- sampleH(); v <- lazy uniform in (0, 1)
    s <- 1; n <- 0                       # s is the partial sum 1 - a_1 + ... +/- a_n
    loop:
      if v > s: break                    # s is an upper bound: reject, restart outer loop
      n <- n + 1; s <- s - a_n(x)        # now an odd partial sum, a lower bound
      if v <= s: return x
      n <- n + 1; s <- s + a_n(x)        # now an even partial sum, an upper bound again
```

The book's version in the exponential form replaces the uniform by an exponential variate (p. 154).

### 15. Kolmogorov-Smirnov law

The following facts describe the sampler:

- Source: Devroye, section IV.5.6 (pp. 161-165), from Devroye (1980). The distribution function is F(x) = the sum over all integers n of (-1)^n exp(-2 n^2 x^2).
- Target: the Kolmogorov-Smirnov limit law.
- Primitives: lazy uniform comparison with enclosures of exp, pi, and a logarithm, so it is exact only in a lazy real model, and an exact exponential sampler.
- Exact: yes in that model.
- Repository: missing.

The constants from the book are as follows:

- Mixture cutoff: any t between sqrt(1/3) and pi/2 works, and the book suggests t = 0.75 (p. 162). Write t' = pi^2 / (8 t^2). Choose the left piece with probability p = F(t), computed from the second series.
- First series, used right of t: c h(x) = 8 x exp(-2x^2) and a_n(x) = (n+1)^2 exp(-2 x^2 ((n+1)^2 - 1)). The terms decrease for x above sqrt(1/3) (Lemma 5.1, p. 162).
- Second series, used left of t, from the theta function transform: c h(x) = (sqrt(2 pi) pi^2 / (4 x^4)) exp(-pi^2 / (8 x^2)), with odd terms (4 x^2 / pi^2) exp(-(n^2 - 1) pi^2 / (8 x^2)) and even terms (n+1)^2 exp(-((n+1)^2 - 1) pi^2 / (8 x^2)). The terms decrease for x below pi/2.
- Right proposal: X = sqrt(t^2 + E/2) for an exponential E has density proportional to x exp(-2x^2) on x at least t (Lemma 5.2, p. 165).
- Left proposal: the book's generator (p. 164) draws X = pi / sqrt(8G) with G = t' + E0 / (1 - 1/(2t')) accepted by the test E0^2 at most t' E1 (G + t'), or by the test G/t' - 1 - log(G/t') at most E1, where E1 is twice an exponential.

The pseudocode follows:

```
kolmogorov():
  if uniform(0,1) < F(t): x <- leftProposal(); run seriesMethod with the second series on x
  else:                   x <- rightProposal(); run seriesMethod with the first series on x
```

### 16. Jöhnk Beta generator

The following facts describe the sampler:

- Source: Devroye, section IX.3 (p. 418), after Jöhnk (1964). The same page gives Berman's variant, which returns X as Beta(a, b+1), and Jöhnk's Gamma generator for shape below 1. Theorem 3.4 (p. 417) proves the rejection step.
- Target: Beta(a, b) for any a and b positive. The acceptance probability is Gamma(a+1) Gamma(b+1) / Gamma(a+b+1), so it is efficient when a and b are at most 1.
- Primitives: the lazy powers U^(1/a) and V^(1/b), a lazy sum and comparison, and one division. The repository has `PSRN.powerRational`, `PSRN.add`, `PSRN.less`, and `PSRN.divide`.
- Exact: yes.
- Repository: missing. `PSRN.newBeta` covers only a and b at least 1.

The pseudocode follows:

```
johnk(a, b):
  loop:
    x <- U^(1/a); y <- V^(1/b)           # lazy reals from fresh uniforms U and V
    if x + y <= 1: return x / (x + y)
```

### 17. Bit-model rejection with interval oracles

The following facts describe the sampler:

- Source: Devroye and Gravel, "Random variate generation using only finitely many unbiased, independently and identically distributed random bits" (arXiv 1502.02539). Section 3.6 (Algorithm 6, pp. 37-38) is bisection with oracles for F and its inverse. Section 3.7 extends von Neumann rejection with infimum and supremum oracles for f on rectangles (3.7.1, compact support, p. 40, with a quadtree; 3.7.2, non-compact support).
- Target: an absolutely continuous law, returned within accuracy epsilon of an exactly distributed value, using unbiased bits only. Theorem 11 (p. 38) bounds the bit cost of bisection by 3 plus log2 of (b - a) / (2 epsilon).
- Primitives: random bits and exact oracles. For rejection, f is Riemann integrable and the oracle returns inf and sup of f over any box.
- Exact: yes, as an exact coupling at accuracy epsilon.
- Repository: partial. `PSRN.newRejection` is a lazy proposal and acceptance engine, and `General.inverseCDF` is related. The interval-oracle quadtree form and its bit accounting are not present.

The pseudocode follows:

```
bisect(F, Finv, a, b, eps):
  while b - a > 2 * eps:
    z <- Finv((F(a) + F(b)) / 2)
    if randomBit() = 0: b <- z else a <- z
  return (a + b) / 2
```

### 18. Homogeneous Poisson process

The following facts describe the sampler:

- Source: Devroye, section VI.1.2 (p. 248), with Theorem 1.1 (p. 247). The book also gives the exponential spacings method (p. 249).
- Target: the points of a Poisson process of rate lambda on [0, T]. A Poisson count with mean lambda T, then that many independent uniform points. The sorted points follow.
- Primitives: `poissonRational` for the count when lambda T is rational, and lazy uniforms ordered by comparison. `PSRN.newOrderStatistic` is related.
- Exact: yes. The points are lazy reals.
- Repository: missing. The Poisson counts exist, but not the process.

The pseudocode follows:

```
poissonProcess(lambda, T):
  n <- poissonRational(lambda * T)
  u <- n independent lazy uniforms; sort u by lazy comparison
  return T * u
```

### 19. Thinning for Poisson processes

The following facts describe the sampler:

- Source: Devroye, section VI.1 (p. 255), the thinning method of Lewis and Shedler, with Theorem 1.3 (p. 254) as its proof. Example 1.4 (p. 256) applies it to the rate lambda(1 + cos t). Theorem 1.5 (p. 258) gives a global alternative.
- Target: a non-homogeneous Poisson process with rate function lambda(t) at most mu(t), for a dominating rate mu that is a rational constant, or a dominating process that candidate 18 simulates.
- Primitives: candidate 18 for the dominating process, and a coin with probability lambda(t) / mu(t) at a lazy time t. Bernoulli factories supply the coin for analytic lambda.
- Exact: yes.
- Repository: missing.

The pseudocode follows:

```
thin(lambda, mu, T):
  keep <- []
  for t in poissonProcess(mu, T):
    if Bernoulli(lambda(t) / mu): keep.append(t)
  return keep
```

### 20. Discrete Gaussian

The following facts describe the sampler:

- Source: Canonne, Kamath, and Steinke, "The Discrete Gaussian for Differential Privacy" (arXiv 2004.00010), Algorithm 3 in section 5.3 (p. 33), with Theorem 32 (p. 30). Algorithm 1 samples Bernoulli(exp(-gamma)) and Algorithm 2 samples the discrete Laplace.
- Target: Pr(X = k) proportional to exp(-k^2 / (2 s)) on the integers, for rational s = sigma^2 greater than 0.
- Primitives: the discrete Laplace sampler with integer scale t and the Bernoulli(exp(-r)) coin for rational r. The repository has `DiscreteExtra.discreteLaplace` (rational epsilon, from the same paper) and `expMinusRational`.
- Exact: yes, with rational arithmetic only, except for t, which needs an integer square root. Expected cost is constant.
- Repository: missing. `gaussianInteger` samples the one-sided variance-one case on the natural numbers.

The pseudocode follows:

```
discreteGaussian(s):                     # s = sigma^2, rational, positive
  t <- floor(sqrt(s)) + 1
  loop:
    y <- discreteLaplace(1, t)           # Pr proportional to exp(-|y| / t)
    r <- (|y| - s / t)^2 / (2 s)
    if Bernoulli(exp(-r)): return y
```

The success probability per round exceeds 0.29, which bounds the cost.

### 21. Ladder chain from a coin

The following facts describe the sampler:

- Source: Morina, Łatuszyński, Nayar, and Wendland, "From the Bernoulli Factory to a Dice Enterprise via Perfect Sampling of Markov Chains" (arXiv 1912.09229). Section 3.4 and Corollary 3.7 (p. 14) give the univariate case. Theorem 3.1 (p. 9) reduces a rational function to a ladder, and Proposition 3.12 (p. 16) bounds the cost.
- Target: with a p-coin, the law Pr(X = i) proportional to R_i p^i (1 - p)^(k-i) on {0, ..., k}, for positive constants R_i. For rational R_i, every comparison is rational, so the sampler is exact. A rational function f(p) maps to such a law through Theorem 3.1, and the multivariate case uses a die.
- Primitives: one p-coin flip B and one uniform U per step, with monotone coupling from the past. The repository has `couplingFromPast`.
- Exact: yes. The number of coin tosses has exponential tails and a mean bounded uniformly in p.
- Repository: missing. `couplingFromPast` and `bernoulliRace` are the reusable parts.

The update function from Corollary 3.7 follows. The chain moves down on tails and up on heads, with acceptance ratios built from the neighbors:

```
phi(i, B, U):
  if i > 0 and B = 0 and U <= R[i-1] / max(R[i-1], R[i]): return i - 1
  if i < k and B = 1 and U <= R[i+1] / max(R[i], R[i+1]): return i + 1
  return i
sample(): run monotone coupling from the past from states 0 and k with shared (B, U) pairs
```

The update is monotone, so two chains started at the extreme states suffice.

### 22. Poisson and logarithmic laws from a coin

The following facts describe the sampler:

- Source: Flajolet, Pelletier, and Soria, "On Buffon machines and numbers" (arXiv 0906.5560). Section 2.1 gives the von Neumann schema (Fig. 3) with Theorem 2.1, and Theorem 2.2 gives the Poisson and logarithmic cases.
- Target: with only a lambda-coin and fair bits, Poisson(lambda) and Logarithmic(lambda) for lambda in (0, 1). Poisson with larger rate follows by adding independent Poisson variates. A choice of the permutation class P gives Pr(N = n) proportional to P_n lambda^n / n!, so the alternating permutations give the secant and tangent laws.
- Primitives: Geometric draws from the lambda-coin and a lazy comparison of the bits of N uniforms (a binary trie).
- Exact: yes. The cost has exponential tails, and the schema needs 1 over (1 - lambda) P(lambda) rounds on average.
- Repository: missing. `poissonOne` and `poissonRational` need a fixed rational rate, and `logarithmicSeries` takes a rational parameter.

The pseudocode follows:

```
vonNeumannSchema(lambdaCoin, inClass):
  loop:
    n <- number of heads before the first tail from lambdaCoin
    u <- n lazy uniforms (bits drawn on demand)
    if order type of u is in inClass(n): return n
# Poisson: inClass(n) = "u is increasing"; Logarithmic: inClass(n) = "u_1 is the largest"
```

Section 2.2 shows that declaring success at one value of N gives the coins exp(-lambda), (1 - lambda) exp(lambda), and lambda exp(1 - lambda), and that the alternating classes give coins such as cos(lambda), (1 - lambda) / cos(lambda), and (1 - lambda) tan(lambda) (Theorem 2.3). The repository already has most of those coins.

### 23. Grammar-driven algebraic coins

The following facts describe the sampler:

- Source: Flajolet, Pelletier, and Soria, sections 3.1 and 3.2. Theorem 3.1 gives the square root, and Theorem 3.2 (after Mossel and Peres) turns a binary stochastic grammar into a coin.
- Target: Bern((1 - lambda) S(lambda / 2)) for a lambda-coin, where S(z) counts the words of a deterministic binary grammar by length. The balanced-walk case with 2N flips gives Bern(sqrt(1 - lambda)). The family with step +(t - 1) gives S(z) equal to the sum of C(tn, n) z^(tn), which is algebraic of degree t.
- Primitives: Geometric draws from the lambda-coin, fair flips, and a pushdown parse of the word. The balanced cases need only a counter.
- Exact: yes.
- Repository: missing as a general construction. `fractionalPower` and `goldenFamily` cover the square root and some algebraic constants, but not grammar-defined functions such as the one from ternary trees.

The pseudocode follows:

```
grammarCoin(lambdaCoin, G, S):
  n <- number of heads before the first tail from lambdaCoin
  w <- n independent fair flips written as H and T
  return 1 if the word w is in the language of G from S, else 0
```

A bridge with steps +2 and -1 (the ternary case, S(z) equal to the sum of C(3n, n) z^(3n)) runs the same way with a counter that moves by +2 or -1.

## Considered and left out

The following items failed a test, and the sources I could read do not contain the others:

- Fristedt integer partitions and Ahrens-Dieter Gamma sampling need real-valued parameters and are approximate.
- Flajolet and Saheb's bit-model exponential and Karney's Gaussian are already covered by `exponential` and `gaussian`.
- Rémy's binary tree algorithm, cycle-lemma Dyck paths, the hook walk for Young tableaux, Ewens permutations by the Feller coupling, permutations with a fixed number of cycles, Floyd's subset algorithm, and Wilson's spanning tree algorithm are not in Devroye's chapters XII and XIII, nor in the other papers that I could open. Devroye's text gives a hashing-based rejection method for classical subset sampling (section XII.2) and covers random binary search trees, which are not uniform (section XIII.2.2, p. 649). I removed these entries rather than cite them from memory.
- Most Buffon machine constants (1/pi, exp(-1), log 2, polylogarithm values, arctan, erf-type integrals, and the sec and tan families) match entries in `Constants`, `Lazy`, and the Bernoulli factories. The full text confirmed that the new material is candidates 22 and 23.
- The inversion-with-correction step of Devroye and Yuen (section XII.3.4) and Devroye's log-concave discrete generator use real-valued powers or densities with no exactness argument.

## Recommended first ten

The following ranking weighs value to users, closeness to existing verified pieces, and proof effort:

1. Discrete Gaussian (20). It reuses two existing samplers and has a short proof in the paper.
2. Forsythe-von Neumann rejection (13). A generic combinator would unify several existing proofs and serve candidates 14 and 15.
3. Prüfer-code labeled trees (1). It is a short bijection proof and opens a tree module.
4. Sequential balanced parentheses (2). It needs one rational comparison per step and gives Catalan objects with a direct counting proof.
5. Homogeneous Poisson process (18). It composes `poissonRational` with lazy order statistics.
6. Set partitions by the Stirling recurrence (3). The proof is a direct counting argument.
7. Integer partitions by Wilf's recurrence (4). It needs bignum tables, and the book leaves the algorithm as an exercise, so the proof is original work.
8. Jöhnk Beta generator (16). It extends `PSRN.newBeta` to small parameters with existing lazy operations.
9. Poisson and logarithmic laws from a coin (22). It adds a coin-driven discrete family with a short proof from the egf identity.
10. Ladder chain from a coin (21). It reuses `couplingFromPast` and gives a new proof pattern.

Close runners-up are the alternating series method (14) with the Kolmogorov-Smirnov law (15), the guide table (10), skip inversion (7), and thinning (19).
