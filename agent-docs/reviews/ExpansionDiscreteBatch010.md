# Expansion discrete review: immutable batch 010

Reviewer: `/root/expand_review_discrete`. Five accepted core samplers.

## `Occil.DiscreteExtra.logarithmicSeries` — accepted (core)

Public specification: `SampLib.LogarithmicSeries.logarithmicSeries_distSpec`.

Source SHA-256: `cde06a1dd5ea7b2177574b821b682af14aa1db308d506b814c9e87b7c5628f79`.

Reciprocal rejection of Geometric(1-p) proposals has mass ((1-p)/p)*(-log(1-p)); normalizing and shifting gives the standard positive-integer logarithmic-series PMF p^(n+1)/((n+1)*(-log(1-p))). The shared AcceptedProposal identity supplies the sole retry-conservation step. CTE performs one geometric proposal, one reciprocal rational coin, and an immediate return or amplified retry. Tests check the first atom at p1/2, no zero atom including infinite credit there, constant infinite expectation and generic resource framing.

## `Occil.multinomial` — accepted (core)

Public specification: `SampLib.Multinomial.multinomial_distSpec`.

Source SHA-256: `218fdbd92c2d4cde984f012821d8cc4d547c885d7f0d3e6b696d015c41808787`.

The public target is the standard List.multinomial PMF with exact length and total-count support, rather than the conditional sampling recurrence. A private conditional-binomial kernel proves its normalization and disintegration. Main CTE is list induction: either the all-zero/zero-trial branch, or a supported binomial head count followed by the tail induction and list cons. Tests check nonuniform joint masses4/9 and1/9 for n2/weights[1,2], zero weight and invalid length/sum masses, zero-trial/all-zero/empty laws, infinite expectation and the actual count-list encoder under generic framing.

## `Occil.weightedWithoutReplacement` — accepted (core)

Public specification: `SampLib.WeightedWithoutReplacement.weightedWithoutReplacement_distSpec`.

Source SHA-256: `e28c30c97b1502a30cd4aae296d900be94bc58261047a1bc87e25454ecbfe7f1`.

The canonical ordered Plackett-Luce law exposes its successive weight/remaining-total product and full-length, distinct, originally-positive support. Reviewer feedback requested these characterizations before acceptance. A supported categorical draw, deterministic coordinate zeroing and finite k induction implement the actual sampler. Tests distinguish order: weights[2,1],k2 gives [0,1] probability2/3 and [1,0] probability1/3; repetitions and short outputs have zero mass. Empty/all-zero zero-request, sole positive label among zeros, infinite credit at repeated labels and generic framing are checked.

## `Occil.Weighted.cumulativeDraw` — accepted (core)

Public specification: `SampLib.CumulativeDraw.cumulativeDraw_distSpec`.

Source SHA-256: `f241a767a4bf46eaa619a7a4968f97b957174f5ddd1c248f9464181b50a3c7c6`.

The independent finite quantile/CDF law includes lower-endpoint atoms. The actual source tests high<=low, so the proof explicitly uses ordered brackets to identify this with equality; every lookup stays in range, and midpoint branches strictly reduce width. Tests use cumulative values[0,2,2,5] with equal CDF probabilities2/5 at1 and2, a positive lower atom2/5, a singleton array/quantile, arbitrary infinite expectations and resource framing. No cdf(lower)=0 hypothesis is introduced.

## `Occil.Weighted.cumulativeChoice` — accepted (core)

Public specification: `SampLib.CumulativeChoice.cumulativeChoice_distSpec`.

Source SHA-256: `2937a52a25c464a1ca82748aaa9c6093104d675b7a735efa24328b0766a544ac`.

The prefix scan constructs the exact categorical CDF. A category-prefix comparison theorem identifies its quantiles with the original categorical rank partition, proving equality with WeightedChoice.law mapped to integer labels. The actual preprocessing scan is verified separately before composing the verified cumulative-table draw. Reviewer feedback replaced two binder-lemma forests by ClosedExp instances. Tests check scan[0,2,0,3]=[0,2,2,5], masses2/5 and3/5 at labels1 and3, infinite credit at zero-weight label0, singleton weight7 arbitrary-F expectation, and generic framing. The deterministic cumulativeTable helper is not counted separately.

## Supporting mathematics and deterministic code

LogarithmicSeries evaluates a nonnegative logarithmic power series and exposes the exact standard PMF. Multinomial defines standard raw count-vector masses independently, then derives normalization/disintegration through its private conditional kernel; zero-tail denominators are handled without invalid cancellation. WeightedSelections exposes the standard ordered likelihood and valid-domain length/distinct/positive-label support. No arbitrary continuation is converted to real or NNReal arithmetic.

FiniteCDF was independently accepted by the structured reviewer in ExpansionStructuredBatch008 and fully source-assessed again here: finite quantiles have the supplied CDF, including lower atoms; fixed-quantile brackets support bisection. CategoricalCDF proves prefix sums and categorical block labels coincide, then identifies the measures. The small syntax helpers use only local closedness for opening and explicit freshness for closing.

NatCounters is independently reviewed supporting code, not another sampler: exact zero-vector construction, indexed increment and positive-entry decrement have full natural domains and no UniformInt requirement. Independent clients frame an arbitrary resource through all three operations and check middle1→0 decrement. The source is pinned before its negative-multinomial/urn consumers.

Support hashes:

- `SampLib.Distributions.LogarithmicSeries`: `7b5b4914e2262bad37148483b414434fa3a9fda12164bb89d6fc28884cf0e2a2`.
- `SampLib.Distributions.Multinomial`: `9253a234cf5994afefa1827f42c9b88aa953b2b30ba98cf35f64a4a83210867f`.
- `SampLib.Distributions.MultinomialCoefficients`: `88f9807f4b18983a0bafbd25be7ad6be5716bef48c5bf2f1f947ffd98d7598f7`.
- `SampLib.Distributions.WeightedSelections`: `c570a0923d0a3a2aee1d77b203cd9dbea594bcfdd0fa5ab55b29b85439a14708`.
- `SampLib.Distributions.WeightedPositiveSupport`: `32ee7e4ff528200c349f10161fb94da8d4bf36e874803a11c4de68bf9de1c1ae`.
- `SampLib.Distributions.FiniteCDF`: `3f82e129e77837788cd13ef0b431cdf6b94ee9cc19440854e3464da6a4cb10f3`.
- `SampLib.Distributions.CategoricalCDF`: `cdabbeed240dbbe859bb6209f8064748c0d5c63724f709395dc579d6fbc1bba5`.
- `SampLib.NatCounters`: `041132bb64a0c8a53c2bdb929635f144b10cd1ae47ceeb2e1a6c3bfbdf65ab15`.
- `SampLib.MarkovTerms`: `acc68951ea3e8a6fd8fca877f1d6cb3874a553761d5037888ef6d874611d0d2c`.
- `SampLib.GeneralSyntax`: `3c097dd0e388f10ac683bd66d88fa3361e2d5631cebe3ab4782e70037123fdef`.
- `SampLib.SamplerTerms`: `57b93ff11099ac98eb55a4b4a04eeb349e58454bb9bd96d040f9c4cbc24a98be`.

## Validation

Independent gated builds of all included modules pass without warnings at default heartbeats. Working and immutable copied callers compile without warnings. Public sampler specs, analytic/PMF/likelihood/CDF identities and NatCounters operations depend only on propext, Classical.choice and Quot.sound. Source formatting/whitespace pass. Normalized typed laws admit arbitrary measurable ENNReal continuation credits, including infinity, with unrelated resources retained.
