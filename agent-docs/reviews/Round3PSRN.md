# Round 3 review: PSRN and Latent

Reviewer: `round3_review_psrn`. Base commit: `8f819b7`.

## Scope

This review covers every file under `SampLib/PSRN/` and `SampLib/Latent/`, including the
committed part of the refactor in `57aa03d` and the uncommitted working tree. It covers the
29 samplers in the lead's sampler list for this group.

## Result

The refactor is accepted. Every change keeps the theorem it proves and reads at least as
clearly as before.

Records cover all 29 samplers. The first draft covers 23. A second draft covers the six
samplers whose caller files needed an import fix first.

## Public specs and proof hashes

The table lists every stale public spec and its new proof hash, exactly as
`refactor_receipts.py --list` prints them. No historical rows are stale.

| Record | Sampler | Public spec | Proof hash |
| --- | --- | --- | --- |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newGammaInteger` | `SampLib.PSRNGammaInteger.newGammaInteger_latentDistSpec` | `d8e49b905519340c721f4f16c205c064b70eecfb822b44690f67ab50af879d58` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newGammaMixture` | `SampLib.PSRNGammaMixture.newGammaMixture_latentDistSpec` | `62525bb93c93dda113604c4e8905bf377cbc95605426b58a64c758ec50620a6d` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newLindley` | `SampLib.PSRNLindley.newLindley_latentDistSpec` | `eebfb0896a257a88b93610d8dbd79927c8fd681b7ac21ae2263d72a47d5ffa56` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.coin` | `SampLib.LatentReal.Coin.coin_programSpec` | `548db82062c52f33f6dc95a0678c3457447de9bc36654b9f67b9fa25d6d29c97` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newInsideShape` | `SampLib.PSRNInsideShape.newInsideShape_vectorSpec` | `72ec8482d9a731697ce24f04214097e53208bb47ab88956d9736307e735473bd` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newRejection` | `SampLib.PSRNRejection.newRejection_latentDistSpec` | `65d5dbefaaeb253b423032a6402f3f89815aa50ba0d525b5106a5a3248a974e2` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newUniform` | `SampLib.LatentUniform.newUniform_latentDistSpec` | `bb0812fce158c74d487ebe10facdad0f8b0bef23b0716a7fa62cc5d045330032` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newGarima` | `SampLib.PSRNGammaFamilies.newGarima_latentDistSpec` | `a7713f036d9d86d55e7a6a6f14403197b95aa75a7cb1fe2d83dfd59971fa7525` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newIGarima` | `SampLib.PSRNGammaFamilies.newIGarima_latentDistSpec` | `a7713f036d9d86d55e7a6a6f14403197b95aa75a7cb1fe2d83dfd59971fa7525` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newMirra` | `SampLib.PSRNGammaFamilies.newMirra_latentDistSpec` | `a7713f036d9d86d55e7a6a6f14403197b95aa75a7cb1fe2d83dfd59971fa7525` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newRayleigh` | `SampLib.PSRNRayleigh.newRayleigh_latentDistSpec` | `4c4846b6a8dbc04540e1d39b1b59b00eee14df711bc318c98753c6f826068f01` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newSushila` | `SampLib.PSRNLindleyFamilies.newSushila_latentDistSpec` | `eee3ddca6c7694f16933d6fe92a074065ea884aec87e4091f361c2a611dffaa3` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newWeightedExponentialGamma` | `SampLib.PSRNGammaFamilies.newWeightedExponentialGamma_latentDistSpec` | `a7713f036d9d86d55e7a6a6f14403197b95aa75a7cb1fe2d83dfd59971fa7525` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newXLindley` | `SampLib.PSRNLindleyFamilies.newXLindley_latentDistSpec` | `eee3ddca6c7694f16933d6fe92a074065ea884aec87e4091f361c2a611dffaa3` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newXgamma` | `SampLib.PSRNGammaFamilies.newXgamma_latentDistSpec` | `a7713f036d9d86d55e7a6a6f14403197b95aa75a7cb1fe2d83dfd59971fa7525` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.expMinusCoin` | `SampLib.LatentReal.ExpMinusCoin.expMinusCoin_programSpec` | `ca1f83567a71da4da22019d4f3d8466d1045f4de3669591d48395c1aeea1b078` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newExponential` | `SampLib.PSRNExponential.newExponential_latentDistSpec` | `bdd247ef4a267a3d4eac2508b288e4b8ccce356f1e05b9588e094104bbf1997c` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newExponentialFromDecay` | `SampLib.PSRNExponential.newExponentialFromDecay_latentDistSpec` | `dd165bc75f8515d9160a67532254f96f711bd1a3314ae1028e79406e8caf582b` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newExponentialLogRate` | `SampLib.PSRNExponential.newExponentialLogRate_latentDistSpec` | `98ab634c9eaeb2a226b450b0d106de4936552a68f85cedd2cac9a96f757cb1e9` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newExponentialUnknownRate` | `SampLib.PSRNExponential.newExponentialUnknownRate_latentDistSpec` | `872c32fe66d2f3791bbc9c4c8ec929d7caaca56c387db4efc4b139b001089041` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newSimplex` | `SampLib.PSRNSimplex.newSimplex_vectorSpec` | `27e52ae10e6bc5c8d4a58dd0dd88cab621bec44cd70662f46378861815107031` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newByDigits` | `SampLib.LatentDigits.newByDigits_latentDistSpec` | `40de6f6aefd71d574e8dc342bba327b7cbd0dbed44f82b315015d7ea4f393bc4` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newOddsUniform` | `SampLib.PSRNOddsUniform.newOddsUniform_latentDistSpec` | `5edb044dca5a5795bb2422f6861b0bdaf9957361e0d41fbd7b255d45de52fe20` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newPowerUniform` | `SampLib.PSRNPowerUniform.newPowerUniform_latentDistSpec` | `043269f11907890ca817b15e60463d170af5d8ef3940a5597d8b6be56d38886c` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newRatioUniforms` | `SampLib.PSRNRatioUniforms.newRatioUniforms_latentDistSpec` | `e00e89e349b5d271637ef6bdd570149e0be9033d7202eeb2a84a91ecd0848c06` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newReciprocalPowerUniform` | `SampLib.PSRNReciprocalPowerUniform.newReciprocalPowerUniform_latentDistSpec` | `69974517d31ccdb676bbad63677e32d0453a3b83574c4e7ca1f6414d86ccb2ed` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newReciprocalUniform` | `SampLib.PSRNReciprocalUniform.newReciprocalUniform_latentDistSpec` | `ab6f18d1a0276a869916996ce9c884ceb51d504ecdf7f6ba2e93882927d51628` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.newUniformSum` | `SampLib.PSRNUniformSum.newUniformSum_latentDistSpec` | `2c4b4c9bff462c1dbb2445e280e1df3e65700e212c0a4592e4af40e01d2dd929` |
| Exact (`/root/review_exact_b`) | `Occil.PSRN.powerCoin` | `SampLib.PSRNPowerCoin.powerCoin_distSpec` | `a150054377447187e1e718737ce0253b378668111bbac9e95f668326524aeb1e` |

## What I checked

- **Statements.** No public statement changes in the diff. Statement equality rests on the
  lead's mechanical pin check with `statement_pins.py`, which was still in progress when I
  wrote this report. Definitions that appear in spec types, such as
  `SampLib.LatentReal.Model`, `Model.SameWorld`, `UniformBag.rank`,
  `UniformBag.readRefines`, `UniformVector.world`, `UniformVector.view`, and
  `UniformVector.initial`, move to new `Latent/Laws/` modules under the same namespaces.
- **Moves and merges.** I compared every top-level declaration block of the 148 base files
  against the 135 current files, ignoring whitespace. Apart from the changes listed below,
  every block reappears verbatim under the same fully qualified name. This covers the 97
  module moves in the author's list, including the 21 merges into their users.
- **Deleted lemmas.** The refactor deletes 21 unused lemmas, such as
  `LatentCoin.credit_add_const`, `ExponentialDigits.conditional_half`,
  `Model.SameWorld.comparison_mass_tendsto`, and `PSRNSimplex.Program.sample_opened`. No
  file in `SampLib/` or `agent-docs/` refers to any of them.
- **Changed proofs.** `Support/Events/RejectionKernel.lean` and
  `Support/Exponential/Logistic.lean` now use `Retry.twp_loop`. Each round body is
  unchanged, and the retry branch passes its credit straight to the induction hypothesis.
  `Syntax/PSRNExpMinusCoin.lean` names the trial body `wholeTail` and states the
  unfolding `sourceBody_eq`, which removes a `set_option maxHeartbeats 800000`.
- **Retry fit.** The remaining users of `ErrorCredit.Induction.simple` in scope,
  `Exponential/Decay.lean`, `Exponential/CoinExponential.lean`, and
  `Latent/UniformBagLess.lean`, are on the brief's list of proofs to leave.
- **Math and program split.** Every `Laws/` module in scope imports only mathlib and other
  `Laws/` modules. `Support/UniformThreshold` moves out of `Laws/`, and the product, root,
  and coin-exponential models move into `Laws/`.
- **Hygiene.** No file in scope contains `sorry`, `admit`, `axiom`, or `native_decide`. No
  line exceeds 100 columns. Every module has a `/-! # Title` docstring.
- **Callers and axioms.** All 16 reviewer caller files compile with no errors and no
  warnings, and their `#print axioms` output lists only `propext`, `Classical.choice`, and
  `Quot.sound`. Four caller files imported modules that the refactor renamed. The lead
  updated only those import lines:
  `ExactConditionalCoinBatch001Callers.lean` and `ExactConditionalCoinBatch002Callers.lean`
  now import `SampLib.PSRN.Support.Arithmetic.Rational`, `ExactLatentBatch006Callers.lean`
  imports `SampLib.PSRN.Support.Exponential.Callbacks`, and
  `ExactLatentBatch007Callers.lean` imports
  `SampLib.PSRN.Support.Represented.ExponentialWrappers`. A diff against the base commit
  confirms that nothing else in those files changes. The lead also deleted the stale build
  files of the removed modules before I compiled the four callers again.

## Nits

These nits do not block acceptance.

- `Support/Events/RejectionKernel.lean:95-96` keeps an `iintro Hcredit` and
  `irevert Hcredit` pair that now does nothing. `Exponential/Logistic.lean` drops it.
- Merged files keep the seams of their sources: each closes and reopens the same
  namespace, as in `Support/Simplex/Model.lean:77-79` and `112-118`.
- `Syntax/PSRNRoot.lean:48` keeps `set_option maxHeartbeats 600000`.
- `Laws/CoinExponentialKernel.lean:11` opens `ProbLang`, and its import of
  `Bernoulli.Laws.ExpMinusFactory` reaches `Metrology.TotalEris` through `Common/Laws/`.
  The leak predates this round.
- Three files exceed 250 lines: `Support/Represented/IntegerPower.lean` (287),
  `Support/Represented/Reciprocal.lean` (268), and `Latent/Laws/Interval.lean` (257).
  All three are unchanged moves.
