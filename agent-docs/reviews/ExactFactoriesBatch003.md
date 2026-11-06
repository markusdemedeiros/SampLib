# Exact factories batch 003

Reviewer: `/root/review_exact_a`.

The five specifications execute the actual factorial-enclosure source programs. Named e/3 and e/4 wrappers inherit the scaled-enclosure argument. The positive integer reciprocal-shift construction uses the already verified rational reciprocal enclosures, with its own exact source encoding proof. The e-2 and 3-e programs use affine and reflected factorial intervals; reflection preserves interval width, so existing tightness gives termination. All five are classified derived, with simple deterministic source execution and a single existing FromBounds or EScaled specification call.

Independent callers preserve arbitrary Iris resources and arbitrary extended continuation credits. They include infinite credits for both outcomes, every c>=1 in the reciprocal family, explicit c=1 and c=2 boundary instances, and identifications of the advertised real biases. Initial affine and reflected source interval tuples are checked exactly. Main CTE proofs use named guard/source-encoding facts; mathematical interval algebra is separated into supporting lemmas.

## Accepted sources

- `Occil.Constants.eDivThree`: `SampLib.EulerScaledConstants.eDivThree_distSpec`; source SHA256 `db36a43c18f1d531ce92b5f012441c2d4f2fa5de3edcbc4d1410fe8efd161695`.
- `Occil.Constants.eQuarter`: `SampLib.EulerScaledConstants.eQuarter_distSpec`; source SHA256 `db36a43c18f1d531ce92b5f012441c2d4f2fa5de3edcbc4d1410fe8efd161695`.
- `Occil.Constants.inverseEPlus`: `SampLib.InverseEPlus.inverseEPlus_distSpec`; source SHA256 `b455b815ced7eb4d3642b299d913aee64b1e52da6d46084f764cb6019688ebfe`.
- `Occil.Constants.eMinusTwo`: `SampLib.EulerAffineConstants.eMinusTwo_distSpec`; source SHA256 `cf608ac66f18bc6e5b22dde484691d700e1e7054bd06248cc8f43a9a4406748a`.
- `Occil.Constants.threeMinusE`: `SampLib.EulerAffineConstants.threeMinusE_distSpec`; source SHA256 `cf608ac66f18bc6e5b22dde484691d700e1e7054bd06248cc8f43a9a4406748a`.

## Evidence

Independent caller: [ExactFactoriesBatch003Callers.lean](ExactFactoriesBatch003Callers.lean).
The caller compiled without warnings or errors under the pinned `06a7b3e2` dependency context.
Every printed public specification uses only `propext`, `Classical.choice`, `Quot.sound`.
The receipt binds the complete project-local source closure and configuration/dependency context.
All implementation source files are unchanged from the frozen campaign baseline.
