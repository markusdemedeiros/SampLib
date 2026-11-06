#!/usr/bin/env python3
"""Statistical checks on actual ProbLang interpreter outputs; Python stdlib only.

Analytic PMFs/CDFs are independent of the object-language implementations.
Every experiment is seeded; no rerolls on failure. Defaults: 8,000 draws/case.
Bin frequencies use Bernstein bounds, continuous CDFs use DKW bounds.
Per-bound alpha=1e-9; moment checks use a separate conservative 8-sigma diagnostic.
These are implementation tests, not proofs of distribution or termination.
"""
import argparse
import collections
import itertools
import json
import math
from pathlib import Path
import statistics
import struct
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/sampler-samples'
LOG = math.log(2 / 1e-9)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def decode(x):
    if isinstance(x, str) and x.startswith('f64:'):
        return struct.unpack('>d', int(x[4:]).to_bytes(8, 'big'))[0]
    if isinstance(x, list):
        return [decode(y) for y in x]
    return x


def draw(name, n, seed, engine='env', timeout=120):
    p = subprocess.run([str(EXE), name, str(n), str(seed), engine],
                       text=True, capture_output=True, timeout=timeout)
    require(p.returncode == 0, f'{name}/{engine}: interpreter failure: {p.stderr}')
    xs = decode(json.loads(p.stdout))
    require(len(xs) == n, f'{name}: wrong sample count')
    return xs


def freeze(x):
    return tuple(freeze(y) for y in x) if isinstance(x, list) else x


def frequencies(xs, pmf):
    counts = collections.Counter(map(freeze, xs))
    require(set(counts) <= set(pmf), f'outside support: {set(counts)-set(pmf)}')
    require(abs(sum(pmf.values()) - 1) < 1e-9, 'reference PMF not normalized')
    chi2 = 0.0
    for x, p in pmf.items():
        obs, expected = counts[x], len(xs) * p
        if p == 0:
            require(obs == 0, f'zero-probability outcome {x}')
            continue
        bound = math.sqrt(2 * len(xs) * p * (1-p) * LOG) + 2 * LOG / 3
        require(abs(obs-expected) <= bound,
                f'frequency {x}: observed {obs}, expected {expected:.2f}, bound {bound:.2f}')
        chi2 += (obs-expected)**2/expected
    return {'chi2_diagnostic': chi2, 'categories': len(pmf)}


def continuous(xs, cdf, support, mean, variance, second=None, fourth=None):
    require(all(type(x) is float and math.isfinite(x) and support(x) for x in xs),
            'nonfinite, wrong-type, or out-of-support real')
    ys = sorted(xs)
    n = len(ys)
    d = max(max((i+1)/n-cdf(x), cdf(x)-i/n) for i, x in enumerate(ys))
    bound = math.sqrt(LOG/(2*n))
    require(d <= bound, f'CDF discrepancy {d:.5f} > DKW bound {bound:.5f}')
    observed = statistics.fmean(xs)
    require(abs(observed-mean) <= 8*math.sqrt(variance/n) + 1e-12,
            f'mean {observed} differs from {mean}')
    if second is not None:
        m2 = statistics.fmean(x*x for x in xs)
        require(abs(m2-second) <= 8*math.sqrt((fourth-second*second)/n)+1e-12,
                f'second moment {m2} differs from {second}')
    return {'mean': observed, 'variance': statistics.pvariance(xs),
            'ks': d, 'ks_bound': bound}


def uniform(items):
    items = list(items)
    return {freeze(x): 1/len(items) for x in items}


def binomial(n, p):
    return {k: math.comb(n, k)*p**k*(1-p)**(n-k) for k in range(n+1)}


def compositions(total, n, minimum):
    if n == 1:
        return [(total,)] if total >= minimum else []
    return [(i,)+tail for i in range(minimum, total-minimum*(n-1)+1)
            for tail in compositions(total-i, n-1, minimum)]


def beta_cdf_integer(x, a, b):
    if x <= 0: return 0.0
    if x >= 1: return 1.0
    n = a+b-1
    return sum(math.comb(n, j)*x**j*(1-x)**(n-j) for j in range(a, n+1))


def check(name, xs):
    n = len(xs)
    coins = {
        'rational': .4, 'real_coin': .3, 'fair': .5, 'complement': .6,
        'product': .4*.75, 'disjunction': 1-.6*.25, 'mean': (.4+.75)/2,
        'conditional': .4/3+.75*2/3, 'extractor': .5, 'race': .4/(.4+.75),
        'one_div': 1/1.4, 'even_parity': 1/1.4, 'sqrt': math.sqrt(.4),
        'power_two_thirds': .4**(2/3), 'exp_rational_small': math.exp(-.4),
        'exp_rational_large': math.exp(-7/3), 'exp_factory': math.exp(-.4),
         'exp_half': math.exp(-.5), 'edge_one_div1': .5,
        'logistic': .6/1.6, 'pgf': math.exp((.4-1)*7/3),
        'bernstein': .2*.6**2 + 2*.5*.4*.6 + .8*.4**2,
        'bag_compare': .4, 'geometric_bag': .5, 'exp_martingale': math.exp(-.4),
        'cosine_factory': math.cos(.4), 'sine_factory': math.sin(.4),
        'log_factory': math.log1p(.4), 'arctan_over_p': math.atan(.4)/.4,
        'arctan_factory': math.atan(.4),
        'cosine_one': math.cos(1), 'sine_one': math.sin(1), 'log_one': math.log(2),
        'arctan_one': math.pi/4, 'exp_martingale_one': math.exp(-1),
        'edge_exp_factory1': math.exp(-1),
        'low_probability_boundary': 1/4, 'low_probability_interior': 3/8,
        'low_probability_contracting': 1/4,
    }
    if name in coins:
        require(all(type(x) is bool for x in xs), 'non-Boolean coin output')
        p = coins[name]
        return frequencies(xs, {True: p, False: 1-p})
    ranges = {'uniform7': range(7), 'inclusive6': range(7), 'range': range(-3, 5),
              'range_exc': range(-3, 4), 'fdr7': range(7), 'fdr257': range(257),
              'mod_small': range(4), 'mod_equal': range(11), 'mod_large': range(17),
              'choice': [10, 20, 30, 40]}
    if name in ranges:
        require(all(type(x) is int for x in xs), 'non-integer output')
        return frequencies(xs, uniform(ranges[name]))
    if name == 'binomial': return frequencies(xs, binomial(12, .4))
    if name == 'bounded_geometric':
        return frequencies(xs, {**{k: .2*.8**k for k in range(7)}, 7: .8**7})
    if name == 'weighted_rejection':
        return frequencies(xs, {0: .1, 1: 0, 2: .3, 3: .6})
    if name == 'weighted_without_replacement':
        return frequencies(xs, {(i,j): (i+1)/6*(j+1)/(6-i-1)
                                for i in range(3) for j in range(3) if i!=j})
    if name == 'alias_balanced':
        return frequencies(xs, uniform(itertools.product(range(3), repeat=3)))
    if name == 'alias':
        ps = {0: .1, 2: .3, 3: .6}
        return frequencies(xs, {v: math.prod(ps[i] for i in v)
                                for v in itertools.product(ps, repeat=3)})
    if name in ('sattolo', 'derangement'):
        permutations = list(itertools.permutations(range(4)))
        if name == 'derangement':
            permutations = [p for p in permutations if all(i!=p[i] for i in range(4))]
        else:
            def one_cycle(p):
                seen, i = set(), 0
                while i not in seen:
                    seen.add(i)
                    i = p[i]
                return len(seen)==4 and i==0
            permutations = [p for p in permutations if one_cycle(p)]
        return frequencies(xs, uniform(permutations))
    if name == 'flip_bits':
        original = [True, False, True]
        return frequencies(xs, {v: math.prod(2/3 if b==o else 1/3 for b,o in zip(v,original))
                                for v in itertools.product([True, False], repeat=3)})
    if name == 'bag_prefix': return frequencies(xs, uniform(range(256)))
    if name == 'bag_reread':
        require(all(len(v)==2 and v[0]==v[1] for v in xs), 'cached prefix changed')
        return frequencies([v[0] for v in xs], uniform(range(256)))
    if name == 'bag_compare_joint':
        return frequencies(xs, {(True,True): .25, (False,True): .5, (False,False): .25})
    if name == 'geometric_bag_joint':
        return frequencies(xs, {(True,True): 1/3, (True,False): 1/6,
                                (False,True): 1/6, (False,False): 1/3})
    if name in ('poisson_one', 'poisson_rational'):
        require(all(type(x) is int and x >= 0 for x in xs), 'invalid Poisson output')
        rate = 1 if name == 'poisson_one' else 7/3
        pmf = {k: math.exp(-rate)*rate**k/math.factorial(k) for k in range(16)}
        pmf['tail'] = 1-sum(pmf.values())
        return frequencies([x if x < 16 else 'tail' for x in xs], pmf)
    if name in ('geometric', 'negative_binomial'):
        require(all(type(x) is int and x >= 0 for x in xs), 'invalid failure count')
        r = 1 if name == 'geometric' else 3
        pmf = {k: math.comb(k+r-1, k)*.4**r*.6**k for k in range(25)}
        pmf['tail'] = 1-sum(pmf.values())
        return frequencies([x if x < 25 else 'tail' for x in xs], pmf)
    if name == 'dice':
        counts = collections.Counter(map(sum, itertools.product(range(1, 7), repeat=3)))
        return frequencies(xs, {k: c/216 for k, c in counts.items()})
    if name == 'weighted': return frequencies(xs, {0: .1, 1: 0, 2: .3, 3: .6})
    if name == 'multinomial':
        require(all(len(x)==4 and all(type(v) is int and v>=0 for v in x)
                    and sum(x)==10 and x[1]==0 for x in xs), 'invalid multinomial vector')
        pmf = {}
        for a in range(11):
            for b in range(11-a):
                c = 10-a-b
                pmf[(a, 0, b, c)] = math.factorial(10)/math.prod(
                    math.factorial(k) for k in [a,b,c])*.1**a*.3**b*.6**c
        return frequencies(xs, pmf)
    if name == 'polya':
        # Beta-binomial(8,2,3); integer rising factorial reference.
        rising = lambda a, k: math.prod(range(a, a+k))
        return frequencies(xs, {k: math.comb(8,k)*rising(2,k)*rising(3,8-k)/rising(5,8)
                                for k in range(9)})
    if name == 'hypergeometric':
        return frequencies(xs, {k: math.comb(4,k)*math.comb(6,5-k)/math.comb(10,5)
                                for k in range(5)})
    if name == 'walk':
        return frequencies(xs, {2*k-12: p for k,p in binomial(12,.5).items()})
    if name == 'replacement':
        return frequencies(xs, uniform(itertools.product(range(3), repeat=3)))
    if name == 'without_replacement':
        return frequencies(xs, uniform(itertools.permutations(range(5), 3)))
    if name == 'in_order':
        return frequencies(xs, uniform(itertools.combinations(range(5), 3)))
    if name == 'shuffle':
        return frequencies(xs, uniform(itertools.permutations(range(4))))
    if name == 'reservoir':
        require(all(len(x)==3 and len(set(x))==3 for x in xs), 'invalid reservoir')
        return frequencies([sorted(x) for x in xs], uniform(itertools.combinations(range(6),3)))
    if name == 'composition': return frequencies(xs, uniform(compositions(7,3,1)))
    if name == 'weak_composition': return frequencies(xs, uniform(compositions(4,3,0)))
    if name == 'graph':
        edges = list(itertools.combinations(range(5), 2))
        require(all(len(x)==len(set(map(tuple,x))) and set(map(tuple,x))<=set(edges) for x in xs),
                'invalid graph')
        # Check the full 1,024-outcome joint law, including edge independence.
        mask = lambda es: sum(1 << edges.index(tuple(e)) for e in es)
        return frequencies([mask(x) for x in xs],
            {m: (1/3)**m.bit_count()*(2/3)**(10-m.bit_count()) for m in range(1024)})
    if name == 'mixture': return frequencies(xs, {-2: 1/3, 5: 2/3})
    positive = lambda x: x >= 0
    unit = lambda x: 0 <= x <= 1
    if name == 'exponential':
        return continuous(xs, lambda x: -math.expm1(-x), positive, 1, 1, 2, 24)
    if name == 'laplace':
        return continuous(xs, lambda x: .5*math.exp(x) if x<0 else 1-.5*math.exp(-x),
                          lambda x: True, 0, 2, 2, 24)
    if name == 'erlang':
        return continuous(xs, lambda x: 1-math.exp(-x)*(1+x+x*x/2), positive, 3, 3, 12, 360)
    if name == 'uniform_sum':
        def cdf(x):
            return sum((-1)**k*math.comb(3,k)*max(x-k,0)**3 for k in range(4))/6
        return continuous(xs, cdf, lambda x: 0<=x<=3, 1.5, .25)
    if name == 'uniform_min':
        return continuous(xs, lambda x: 1-(1-x)**2, unit, 1/3, 1/18)
    if name == 'uniform_max':
        return continuous(xs, lambda x: x*x, unit, 2/3, 1/18)
    if name == 'order_statistic':
        return continuous(xs, lambda x: beta_cdf_integer(x,2,5), unit, 2/7, 10/(49*8))
    if name == 'gaussian':
        return continuous(xs, lambda x: .5*math.erfc(-x/math.sqrt(2)), lambda x: True,
                          0, 1, 1, 3)
    deterministic = {
         'edge_exp_martingale0': True, 'edge_bounded0': 5, 'edge_alias_single': [1,1,1], 'edge_sattolo_empty': [],
        'edge_derangement0': [], 'edge_bag_zero': False, 'edge_bag_one': True,
        'edge_cos0': True, 'edge_sin0': False, 'edge_log0': False, 'edge_atan0': True,
        'edge_zero_coin': False, 'edge_one_coin': True, 'edge_fdr1': 0, 'edge_rnd0': 0,
        'edge_real_zero': False, 'edge_real_one': True, 'edge_poisson0': 0,
        'edge_binomial0': 0, 'edge_binomial1': 5, 'edge_geometric1': 0,
        'edge_neg_binomial0': 0, 'edge_shuffle_empty': [], 'edge_shuffle_single': [9],
        'edge_reservoir0': [], 'edge_sample0': [], 'edge_in_order_all': [0,1,2],
        'edge_composition': [1,1,1], 'edge_weak0': [0,0,0], 'edge_power1': True,
        'edge_exp0': True, 'edge_exp_factory0': True, 'edge_uniform_sum0': 0.0,
        'edge_low_probability_zero_bound': False, 'edge_low_probability_zero': False,
    }
    require(name in deterministic, f'missing statistical oracle: {name}')
    require(all(x == deterministic[name] and type(x) is type(deterministic[name]) for x in xs),
            f'incorrect boundary output for {name}')
    return {'deterministic': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--count', type=int, default=8000)
    parser.add_argument('--seed', type=int, default=20261105)
    parser.add_argument('--case', action='append', help='limit to selected cases')
    parser.add_argument('--report', type=Path, default=ROOT/'tests/latest-results.json')
    parser.add_argument('--raw-dir', type=Path, help='optional raw values per case')
    args = parser.parse_args()
    require(args.count >= 1000, 'use at least 1,000 draws for statistical tests')
    names = json.loads(subprocess.check_output([str(EXE), '--list'], text=True))
    if args.case:
        require(set(args.case)<=set(names), 'unknown requested case')
        names = [n for n in names if n in args.case]
    results, failures = [], []
    start = time.monotonic()
    for i, name in enumerate(names):
        seed = args.seed + i*104729
        t = time.monotonic()
        try:
            if name.startswith('invalid_'):
                for engine in ['env', 'subst']:
                    p = subprocess.run([str(EXE), name, '1', str(seed), engine],
                                       capture_output=True, text=True, timeout=20)
                    require(p.returncode != 0 and 'stuck: fail' in p.stderr,
                            f'{name}/{engine}: expected explicit failure, got {p.stderr!r}')
                details = {'expected_failure': True, 'samples': 0}
            else:
                n = min(args.count, 100) if name.startswith('edge_') and name not in (
                    'edge_one_div1','edge_exp_factory1') else args.count
                xs = draw(name, n, seed)
                details = {'samples': n, **check(name, xs)}
                # Exact seeded output agreement against the upstream substitution interpreter.
                env = draw(name, 12, seed+1, 'env')
                subst = draw(name, 12, seed+1, 'subst')
                require(env == subst, f'{name}: environment/substitution evaluator disagreement')
                details['differential_samples'] = 12
                if args.raw_dir:
                    args.raw_dir.mkdir(parents=True, exist_ok=True)
                    (args.raw_dir/f'{name}.json').write_text(json.dumps(xs)+'\n')
            results.append({'case': name, 'seed': seed, 'passed': True,
                            'seconds': time.monotonic()-t, **details})
            print(f'PASS {name} ({time.monotonic()-t:.2f}s)', flush=True)
        except (AssertionError, subprocess.TimeoutExpired, ValueError) as e:
            failures.append(name)
            results.append({'case': name, 'seed': seed, 'passed': False, 'error': str(e)})
            print(f'FAIL {name}: {e}', flush=True)
    packages = json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    revision = next(p['rev'] for p in packages if p['name'].strip('«»') == 'clutch-lean')
    report = {'base_seed': args.seed, 'requested_count': args.count,
              'clutch_revision': revision,
              'per_bound_alpha': 1e-9, 'seconds': time.monotonic()-start,
              'total_samples': sum(r.get('samples',0) for r in results),
              'passed': len(results)-len(failures), 'failed': len(failures), 'results': results}
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2)+'\n')
    print(f"{report['passed']}/{len(results)} cases passed; {report['total_samples']} samples; "
          f"report: {args.report}")
    raise SystemExit(bool(failures))


if __name__ == '__main__':
    main()
