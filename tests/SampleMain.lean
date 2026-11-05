import Samplers
import Metrology.ProbLang.Interp.BigStepIO
import Lean.Data.Json.FromToJson

/-! Runs the actual closed pl% terms through upstream ProbLang.Interp.
No sampler is implemented in the host runner. Floats travel as exact IEEE bits. -/
open ProbLang Lean
open Occil

private def ints (xs : List Int) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair (.lit (.int x)) tail)) (.inl (.lit .unit))

private def bools (xs : List Bool) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair (.lit (.bool x)) tail)) (.inl (.lit .unit))

private def ratios (xs : List (Int × Int)) : Exp Float :=
  xs.foldr (fun x tail => .inr (.pair
    (.pair (.lit (.int x.1)) (.lit (.int x.2))) tail)) (.inl (.lit .unit))

private def cases : List (String × Exp Float) := [
  ("uniform7", pl(&uniformInt #7)),
  ("inclusive6", pl(&rndInt #6)),
  ("range", pl(&rndIntRange #(-3) #4)),
  ("range_exc", pl(&rndIntExcRange #(-3) #4)),
  ("fdr7", pl(&fastDiceRoller #7)),
  ("fdr257", pl(&fastDiceRoller #257)),
  ("mod_small", pl(&uniformFromModulus #11 #4)),
  ("mod_equal", pl(&uniformFromModulus #11 #11)),
  ("mod_large", pl(&uniformFromModulus #3 #17)),
  ("rational", pl(&rationalCoin #2 #5)),
  ("real_coin", pl(&realCoin #real (0.3 : Float))),
  ("fair", pl(&fairCoin #())),
  ("binomial", pl(&binomial (fun u, &rationalCoin #2 #5) #12)),
  ("geometric", pl(&geometric (fun u, &rationalCoin #2 #5) #())),
  ("negative_binomial", pl(&negativeBinomial (fun u, &rationalCoin #2 #5) #3)),
  ("dice", pl(&dice #3 #6)),
  ("poisson_one", pl(&poissonOne #())),
  ("poisson_rational", pl(&poissonRational #7 #3)),
  ("weighted", pl(&weightedChoice &(ints [1, 0, 3, 6]))),
  ("multinomial", pl(&multinomial #10 &(ints [1, 0, 3, 6]))),
  ("polya", pl(&polyaEggenberger #8 #2 #3 #1)),
  ("hypergeometric", pl(&hypergeometric #5 #4 #6)),
  ("walk", pl(&randomWalk #12)),
  ("choice", pl(&choice &(ints [10, 20, 30, 40]))),
  ("replacement", pl(&sampleWithReplacement &(ints [0, 1, 2]) #3)),
  ("without_replacement", pl(&sampleWithoutReplacement &(ints [0, 1, 2, 3, 4]) #3)),
  ("in_order", pl(&sampleInOrder &(ints [0, 1, 2, 3, 4]) #3)),
  ("shuffle", pl(&shuffle &(ints [0, 1, 2, 3]))),
  ("reservoir", pl(&reservoir &(ints [0, 1, 2, 3, 4, 5]) #3)),
  ("composition", pl(&positiveComposition #3 #7)),
  ("weak_composition", pl(&weakComposition #3 #4)),
  ("graph", pl(&randomGraph #5 (fun u, &rationalCoin #1 #3))),
  ("complement", pl(&complement (fun u, &rationalCoin #2 #5) #())),
  ("product", pl(&coinProduct (fun u, &rationalCoin #2 #5)
    (fun u, &rationalCoin #3 #4) #())),
  ("disjunction", pl(&coinDisjunction (fun u, &rationalCoin #2 #5)
    (fun u, &rationalCoin #3 #4) #())),
  ("mean", pl(&coinMean (fun u, &rationalCoin #2 #5)
    (fun u, &rationalCoin #3 #4) #())),
  ("conditional", pl(&coinConditional (fun u, &rationalCoin #2 #5)
    (fun u, &rationalCoin #3 #4) (fun u, &rationalCoin #1 #3) #())),
  ("extractor", pl(&vonNeumann (fun u, &rationalCoin #1 #5) #())),
  ("race", pl(&bernoulliRace (fun u, &rationalCoin #2 #5)
    (fun u, &rationalCoin #3 #4) #())),
  ("one_div", pl(&oneDivOnePlus (fun u, &rationalCoin #2 #5) #())),
  ("even_parity", pl(&evenParity (fun u, &rationalCoin #2 #5) #())),
  ("sqrt", pl(&fractionalPower (fun u, &rationalCoin #2 #5) #1 #2 #())),
  ("power_two_thirds", pl(&fractionalPower (fun u, &rationalCoin #2 #5) #2 #3 #())),
  ("exp_rational_small", pl(&expMinusRational #2 #5 #())),
  ("exp_rational_large", pl(&expMinusRational #7 #3 #())),
  ("exp_factory", pl(&expMinusFactory (fun u, &rationalCoin #2 #5) #())),
  ("exponential", pl(&exponential #())),
  ("laplace", pl(&laplace #())),
  ("erlang", pl(&erlang #3)),
  ("uniform_sum", pl(&uniformSum #3)),
  ("uniform_min", pl(&uniformMin #())),
  ("uniform_max", pl(&uniformMax #())),
  ("order_statistic", pl(&orderStatistic #6 #2)),
  ("mixture", pl(&mixture (fun u, &rationalCoin #1 #3)
    (fun u, #(-2)) (fun u, #5) #())),
  ("exp_half", pl(&expHalfCoin #())),
  ("gaussian", pl(&gaussian #())),
  ("bounded_geometric", pl(&boundedGeometric (fun u, &rationalCoin #1 #5) #7)),
  ("weighted_rejection", pl(&weightedRejection &(ints [1, 0, 3, 6]) #6)),
  ("weighted_without_replacement", pl(&weightedWithoutReplacement &(ints [1, 2, 3]) #2)),
  ("alias", pl(&aliasSamples &(ints [1, 0, 3, 6]) #3)),
  ("sattolo", pl(&sattolo &(ints [0, 1, 2, 3]))),
  ("derangement", pl(&derangement #4)),
  ("flip_bits", pl(&flipBits &(bools [true, false, true])
    (fun u, &rationalCoin #1 #3))),
  ("logistic", pl(&logisticFactory (fun u, &rationalCoin #2 #5) #3 #2 #())),
  ("pgf", pl(&probabilityGeneratingFactory (fun u, &rationalCoin #2 #5)
    (fun u, &poissonRational #7 #3) #())),
  ("bernstein", pl(&bernsteinFactory (fun u, &rationalCoin #2 #5)
    &(ratios [(1, 5), (1, 2), (4, 5)]) #())),
  ("bag_prefix", pl(let bag := &newUniformBag #(); &uniformBagPrefix bag #8)),
  ("bag_reread", pl(let bag := &newUniformBag #();
    let a := &uniformBagPrefix bag #8; (a, &uniformBagPrefix bag #8))),
  ("bag_compare", pl(let bag := &newUniformBag #(); &uniformBagLess bag #2 #5)),
  ("bag_compare_joint", pl(let bag := &newUniformBag #();
    let a := &uniformBagLess bag #1 #4; (a, &uniformBagLess bag #3 #4))),
  ("geometric_bag", pl(let bag := &newUniformBag #(); &sampleGeometricBag bag #())),
  ("geometric_bag_joint", pl(let bag := &newUniformBag #();
    let a := &sampleGeometricBag bag #(); (a, &sampleGeometricBag bag #()))),
  ("exp_martingale", pl(&expMinusMartingale (fun u, &rationalCoin #2 #5) #())),
  ("cosine_factory", pl(&cosineFactory (fun u, &rationalCoin #2 #5) #())),
  ("sine_factory", pl(&sineFactory (fun u, &rationalCoin #2 #5) #())),
  ("log_factory", pl(&logOnePlusFactory (fun u, &rationalCoin #2 #5) #())),
  ("arctan_over_p", pl(&arctanOverPFactory (fun u, &rationalCoin #2 #5) #())),
  ("arctan_factory", pl(&arctanFactory (fun u, &rationalCoin #2 #5) #())),
  ("cosine_one", pl(&cosineFactory (fun u, #true) #())),
  ("sine_one", pl(&sineFactory (fun u, #true) #())),
  ("log_one", pl(&logOnePlusFactory (fun u, #true) #())),
  ("arctan_one", pl(&arctanFactory (fun u, #true) #())),
  ("exp_martingale_one", pl(&expMinusMartingale (fun u, #true) #())),
  ("alias_balanced", pl(&aliasSamples &(ints [1, 1, 1]) #3)),
  ("edge_exp_martingale0", pl(&expMinusMartingale (fun u, #false) #())),
  ("edge_bounded0", pl(&boundedGeometric (fun u, #false) #5)),
  ("edge_alias_single", pl(&aliasSamples &(ints [0, 1, 0]) #3)),
  ("edge_sattolo_empty", pl(&sattolo &(ints []))),
  ("edge_derangement0", pl(&derangement #0)),
  ("edge_bag_zero", pl(let bag := &newUniformBag #(); &uniformBagLess bag #0 #3)),
  ("edge_bag_one", pl(let bag := &newUniformBag #(); &uniformBagLess bag #3 #3)),
  ("edge_cos0", pl(&cosineFactory (fun u, #false) #())),
  ("edge_sin0", pl(&sineFactory (fun u, #false) #())),
  ("edge_log0", pl(&logOnePlusFactory (fun u, #false) #())),
  ("edge_atan0", pl(&arctanOverPFactory (fun u, #false) #())),
  ("invalid_alias", pl(&aliasSamples &(ints [0, 0]) #2)),
  ("invalid_rejection_envelope", pl(&weightedRejection &(ints [1, 3]) #2)),
  ("invalid_weighted_subset", pl(&weightedWithoutReplacement &(ints [0, 1]) #2)),
  ("invalid_derangement", pl(&derangement #1)),
  ("invalid_logistic", pl(&logisticFactory (fun u, #true) #0 #1 #())),
  -- Deterministic boundaries, valid empty collections, and failure paths.
  ("edge_zero_coin", pl(&rationalCoin #0 #3)),
  ("edge_real_zero", pl(&realCoin #real (0 : Float))),
  ("edge_real_one", pl(&realCoin #real (1 : Float))),
  ("edge_poisson0", pl(&poissonRational #0 #3)),
  ("edge_one_coin", pl(&rationalCoin #3 #3)),
  ("edge_fdr1", pl(&fastDiceRoller #1)),
  ("edge_rnd0", pl(&rndInt #0)),
  ("edge_binomial0", pl(&binomial (fun u, #true) #0)),
  ("edge_binomial1", pl(&binomial (fun u, #true) #5)),
  ("edge_geometric1", pl(&geometric (fun u, #true) #())),
  ("edge_neg_binomial0", pl(&negativeBinomial (fun u, #false) #0)),
  ("edge_shuffle_empty", pl(&shuffle &(ints []))),
  ("edge_shuffle_single", pl(&shuffle &(ints [9]))),
  ("edge_reservoir0", pl(&reservoir &(ints [0, 1]) #0)),
  ("edge_sample0", pl(&sampleWithoutReplacement &(ints []) #0)),
  ("edge_in_order_all", pl(&sampleInOrder &(ints [0, 1, 2]) #3)),
  ("edge_composition", pl(&positiveComposition #3 #3)),
  ("edge_weak0", pl(&weakComposition #3 #0)),
  ("edge_one_div1", pl(&oneDivOnePlus (fun u, #true) #())),
  ("edge_power1", pl(&fractionalPower (fun u, #true) #1 #2 #())),
  ("edge_exp0", pl(&expMinusRational #0 #3 #())),
  ("edge_exp_factory0", pl(&expMinusFactory (fun u, #false) #())),
  ("edge_exp_factory1", pl(&expMinusFactory (fun u, #true) #())),
  ("edge_uniform_sum0", pl(&uniformSum #0)),
  ("invalid_uniform", pl(&uniformInt #0)),
  ("invalid_modulus", pl(&uniformFromModulus #1 #3)),
  ("invalid_coin", pl(&rationalCoin #4 #3)),
  ("invalid_real_coin", pl(&realCoin #real (-0.1 : Float))),
  ("invalid_poisson", pl(&poissonRational #2 #0)),
  ("invalid_weights", pl(&weightedChoice &(ints [0, 0]))),
  ("invalid_negative_weight", pl(&weightedChoice &(ints [2, -1]))),
  ("invalid_choice", pl(&choice &(ints []))),
  ("invalid_sample", pl(&sampleWithoutReplacement &(ints [0, 1]) #3)),
  ("invalid_composition", pl(&positiveComposition #4 #3)),
  ("invalid_hypergeometric", pl(&hypergeometric #11 #4 #6)),
  ("invalid_order", pl(&orderStatistic #3 #4)),
  ("invalid_erlang", pl(&erlang #0))
]

private partial def encodeValue : Exp Float → Except String Json
  | .lit (.int z) => .ok (toJson z)
  | .lit (.bool b) => .ok (toJson b)
  | .lit (.real r) => if r.isFinite then .ok (.str s!"f64:{r.toBits.toNat}")
      else .error "non-finite real returned"
  | .lit .unit => .ok Json.null
  | .pair x y => do return .arr #[← encodeValue x, ← encodeValue y]
  | .inl (.lit .unit) => .ok (.arr #[])
  | .inr (.pair x xs) => do
      let h ← encodeValue x
      let .arr tail ← encodeValue xs | .error "malformed list tail"
      return .arr (#[h] ++ tail)
  | _ => .error "unexpected output shape (not scalar, pair, or list)"

def main (args : List String) : IO Unit := do
  let stdout ← IO.getStdout
  if args == ["--list"] then
    stdout.putStrLn (toJson (cases.map Prod.fst)).compress
    return
  let [name, countStr, seedStr, engine] := args
    | throw (IO.userError "usage: sampler-samples CASE COUNT SEED env|subst (or --list)")
  let some count := countStr.toNat? | throw (IO.userError "invalid count")
  let some seed := seedStr.toNat? | throw (IO.userError "invalid seed")
  let some (_, term) := cases.find? (fun c => c.1 == name)
    | throw (IO.userError s!"unknown case: {name}")
  unless engine == "env" || engine == "subst" do throw (IO.userError "unknown engine")
  IO.setRandSeed seed
  let mut values : Array Json := #[]
  for _ in [0:count] do
    let value : Exp Float ← if engine == "env" then Interp.eval term else
      (fun cfg => cfg.expr) <$> Interp.runSubst ⟨term, default⟩
    match encodeValue value with
    | .ok j => values := values.push j
    | .error e => throw (IO.userError e)
  stdout.putStrLn (Json.arr values).compress
