# Optimal-matrix certain-row source repair review

Canonical patch author/applier: `/root`. Independent reviewer: `/root/review_exact_a`.
Proposal prepared by `/root/prove_constants`; canonical source remains unchanged at review.

Reviewed file: `code/Samplers/Weighted/Optimal.lean`. Original SHA256 `cc627b9b7e17370238377d0e2d9f0455ab3c465dc20d0b12b67d8e5e63f16d01`; proposed SHA256 `a9b71b1c8b8bfa72602ac4693c83ff2eb0dccb5a98fab661d37c7c534aa44571`.
Byte-exact original: [ExactOptimalOriginalSource.txt](ExactOptimalOriginalSource.txt).

```diff
-          let encoded := (if l = k then m else if l = #0 then m else
+          let encoded := (if m = denominator then ceiling - #1 else
            if l = k then m else if l = #0 then m else
```

The exact replacement occurs once in `optimalMatrix`. Every other byte is preserved;
in particular `optimalDraw`, `optimalChoice`, weight validation, parameter selection,
optional rejection row and traversal logic are unchanged. This review approves the
concrete row encoding repair for the full nonnegative-weight positive-total domain,
including certain distributions with zero-weight categories. It does not replace
that domain by positive-only weights, two categories, or a wrapper shortcut.

## Defect and general argument

I independently derived the boundary defect from the source before reading the
proposal. For generated parameters put A=2^l, P=2^(k-l), C=AP and D=A(P-1).
The preprocessing loop guarantees 0<=l<k, P>=2 and positive D>=total. The first
candidate C-1 is at least total because bitLength(total) gives total<C, so the
fallback l=k is unreachable on valid inputs. Each row m lies in[0,D].

For m<D the original encoder gives E=qP+r, where q=m/(P-1), r=m%(P-1),
q<A and r<P-1. Thus E<C and its cyclic bit mass numerator is
(E/P)(P-1)+E%P=q(P-1)+r=m. These rows are completely unchanged by the patch.
At m=D the old positive-l encoding gives E=AP=C. Every one of its scanned k bits
is zero, so the row cannot be selected. For example [2,0] produces rows[4,0],
k=2,l=1 and no rejection; both scanned columns contain only zero bits and traversal
never returns, whatever the random bits. The author's actual substitution-interpreter
fixture [OptimalCertainRuntime.lean](OptimalCertainRuntime.lean) and its log illustrate
this with three seeds; the all-zero scanned-column argument establishes the defect
independently of bounded runtime observations.

The proposed E=C-1 has quotient A-1 and remainder P-1 modulo P. Its decoded
numerator is (A-1)(P-1)+(P-1)=D. All k bits are one, correctly representing
0.111...=1. Exactly one row can have full mass; all others are zero. On each column
that row returns with probability1/2, leaving one live rank otherwise, hence residual
mass2^(-depth) tends to zero. No expected-time assumption is needed to identify this
endpoint. At l=0 the previous endpoint was already D=C-1, so the patch preserves it.
Zero rows remain zero. No claim about arbitrary malformed hand-built matrices or
unreachable l=k parameter states is introduced.

Independent exact-integer checks in [ExactOptimalEncodingChecks001.json](ExactOptimalEncodingChecks001.json)
cover totals1..512 and all 146151 numerators0..D for the actual selected parameters.
They check row width, exact decoding, zero and l=0 boundaries, old positive-l overflow,
and preservation of every nonendpoint row. They supplement the general argument,
not a formal sampler correctness theorem.

## Scope of approval

This approves only the exact source patch. It does not accept either pending
`Occil.WeightedVariants.optimalChoice` or `Occil.WeightedVariants.optimalDraw`, nor
renew any historical proof/source snapshot. Root must apply the exact bytes after
checkpoint006, register this immutable repair receipt, rebuild dependent proofs and
revalidate current and historical closures. Full general cyclic-matrix construction
and actual traversal CTE theorems remain subject to independent reviewer B acceptance.
No language, dependency or proof-policy change is included.
