# Repair regression expectations

Run only after root applies the independently approved patch:

```
python3 agent-scripts/lean_gate.py -- lake env lean --run agent-docs/reviews/optimal-certain-repair/Regression.lean
```

The runner evaluates actual `pl%` terms with upstream `bigStepF`/`Comp`, using a
100000-transition cutoff for each sampler call. It checks exact preprocessed tables,
then both `optimalChoice` and raw `optimalDraw` at seeds 0, 1, and 99.

Thirteen controls cover both certain positions, an interior certain position with four
zeros, totals 1/2/3/4/5/6, certain inputs with optional rejection, a singleton whose
wrapper shortcut does not exercise the raw draw, balanced/unequal inputs, and zeros
with optional rejection. Singleton supports require the unique indicated result;
other runs must stay in precisely the positive-weight labels. No empirical frequency
threshold substitutes for the formal law or termination proof. A further 75 cases place
the certain category at every position in lengths 1 through 5 for each total
1, 2, 3, 5, and 8; their matrix expectations are explicit fixed profiles.

Expected result: 88 `PASS` lines and the final report of 88 exact matrix checks
and 528 completed sampler runs. The original failing witness and log are unchanged.

The initial repaired Runtime001 hit the old 10000 cutoff on the length-5 certain
case. A separate actual-interpreter profile completed it at seeds 0/1/99 with
17025/13369/15159 transitions for `optimalChoice`, versus 7839/4183/5973 for
`optimalDraw`. The constant 9186-transition difference is preprocessing. The
revised bound accommodates that measured cost; failures still include exact
case, sampler, seed, and transitions. `--profile` repeats this diagnostic case.
