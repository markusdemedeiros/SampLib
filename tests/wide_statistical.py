#!/usr/bin/env python3
"""Numerical regressions and distribution checks on actual ProbLang sampler terms.

Fixed-point outputs are decoded at scale 2^20. Distribution checks have an explicit
finite-grid allowance; they are numerical implementation checks, not exactness
claims or proofs. Python uses independent analytic PMF/CDF references, not samples.
"""
import argparse
import collections
import json
import math
from pathlib import Path
import statistics
import subprocess
import time
import factory_oracles
import vector_oracles
import point_oracles

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/wide-samples'
SCALE = 1048576
ALPHA = 1e-8


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def draw(name, n, seed, engine='env', timeout=180):
    p = subprocess.run([str(EXE), name, str(n), str(seed), engine],
                       capture_output=True, text=True, timeout=timeout)
    require(p.returncode == 0, f'{name}/{engine}: {p.stderr.strip()}')
    xs = json.loads(p.stdout)
    require(len(xs) == n, f'{name}: wrong sample count')
    return xs


def gamma_cdf(x, a, rate=1):
    x *= rate
    if x <= 0: return 0.0
    if x < a+1:
        term = total = 1/a
        for k in range(1, 10000):
            term *= x/(a+k)
            total += term
            if abs(term) < abs(total)*1e-14: break
        return min(1.0, total*math.exp(-x+a*math.log(x)-math.lgamma(a)))
    b, c = x+1-a, 1e300
    d = 1/b
    h = d
    for i in range(1, 10000):
        an = -i*(i-a)
        b += 2
        d = an*d+b
        if abs(d)<1e-300: d=1e-300
        c = b+an/c
        if abs(c)<1e-300: c=1e-300
        d=1/d
        delta=d*c
        h*=delta
        if abs(delta-1)<1e-14: break
    return max(0.0, min(1.0, 1-math.exp(-x+a*math.log(x)-math.lgamma(a))*h))


def beta_cdf(x, a, b):
    if x <= 0: return 0.0
    if x >= 1: return 1.0
    def fraction(a,b,x):
        qab,qap,qam=a+b,a+1,a-1
        c=1.0
        d=1-qab*x/qap
        if abs(d)<1e-300:d=1e-300
        d=1/d;h=d
        for m in range(1,10000):
            aa=m*(b-m)*x/((qam+2*m)*(a+2*m))
            d=1+aa*d;c=1+aa/c
            if abs(d)<1e-300:d=1e-300
            if abs(c)<1e-300:c=1e-300
            d=1/d;h*=d*c
            aa=-(a+m)*(qab+m)*x/((a+2*m)*(qap+2*m))
            d=1+aa*d;c=1+aa/c
            if abs(d)<1e-300:d=1e-300
            if abs(c)<1e-300:c=1e-300
            d=1/d;delta=d*c;h*=delta
            if abs(delta-1)<1e-14:break
        return h
    factor=math.exp(math.lgamma(a+b)-math.lgamma(a)-math.lgamma(b)+a*math.log(x)+b*math.log1p(-x))
    if x < (a+1)/(a+b+2):return factor*fraction(a,b,x)/a
    return 1-factor*fraction(b,a,1-x)/b


def phi(x): return .5*math.erfc(-x/math.sqrt(2))


def poisson_mix(cdf, rate):
    def mixed(x):
        p=math.exp(-rate);total=0
        for k in range(60):
            total+=p*cdf(x,k)
            p*=rate/(k+1)
        return total
    return mixed


def ks(xs, cdf, support=lambda x: True, allowance=.002):
    require(all(math.isfinite(x) and support(x) for x in xs), 'nonfinite or unsupported output')
    ys=sorted(xs);n=len(xs)
    d=max(max((i+1)/n-cdf(x),cdf(x)-i/n) for i,x in enumerate(ys))
    bound=math.sqrt(math.log(2/ALPHA)/(2*n))+allowance
    require(d<=bound, f'CDF discrepancy {d:.5g} exceeds {bound:.5g}')
    return {'ks':d,'bound':bound,'mean':statistics.fmean(xs),
            'variance':statistics.pvariance(xs)}


def frequencies(xs, pmf):
    def freeze(x): return tuple(map(freeze,x)) if isinstance(x,list) else x
    counts=collections.Counter(map(freeze,xs));n=len(xs)
    require(set(counts)<=set(pmf),'outcome outside reference support')
    require(abs(sum(pmf.values())-1)<1e-8,'reference PMF not normalized')
    chi=0
    for value,p in pmf.items():
        obs=counts[value]
        if p==0:require(obs==0,'zero-probability outcome');continue
        bound=math.sqrt(2*n*p*(1-p)*math.log(2/ALPHA))+2*math.log(2/ALPHA)/3
        require(abs(obs-n*p)<=bound,f'frequency {value}: {obs} vs {n*p}')
        chi+=(obs-n*p)**2/(n*p)
    return {'chi2_diagnostic':chi,'categories':len(pmf)}


def irwin_hall(x,n):
    if x<=0:return 0.0
    if x>=n:return 1.0
    if x>n/2:return 1-irwin_hall(n-x,n)
    return sum((-1)**k*math.comb(n,k)*max(x-k,0)**n for k in range(int(x)+1))/math.factorial(n)


def finite_tail(xs, pmf, low=0, high=30):
    require(all(type(x) is int and (low<0 or x>=low) for x in xs),'invalid discrete count')
    reference={k:pmf(k) for k in range(low,high)}
    reference['tail']=max(0,1-sum(reference.values()))
    return frequencies([x if low<=x<high else 'tail' for x in xs],reference)


def poisson_pmf(k,rate):
    return (1.0 if k==0 else 0.0) if rate==0 else math.exp(-rate+k*math.log(rate)-math.lgamma(k+1))


def beta_function(a,b):return math.exp(math.lgamma(a)+math.lgamma(b)-math.lgamma(a+b))


def check_extra(name,raw):
    if name in ('weighted_bits','weighted_bitmask','weighted_fyky','weighted_fixed','general_date','general_inverse_cdf','general_inverse_quantile','general_shape'):
        support={'weighted_bits':range(16),'weighted_bitmask':range(7),'weighted_fyky':range(7),
                 'weighted_fixed':range(13),'general_date':range(-2,4),'general_inverse_cdf':range(4),
                 'general_inverse_quantile':range(1,12),'general_shape':range(0,10,2)}[name]
        return frequencies(raw,{v:1/len(support) for v in support})
    if name in ('weighted_modulo','weighted_shift'):
        function=(lambda k:k%5) if name=='weighted_modulo' else (lambda k:k*5//8)
        counts=collections.Counter(function(k) for k in range(8))
        return frequencies(raw,{v:n/8 for v,n in counts.items()})
    if name in ('weighted_recycler','general_string'):
        import itertools
        return frequencies(raw,{v:1/27 for v in itertools.product(range(3),repeat=3)})
    if name in ('weighted_cumulative','weighted_knuth_yao','weighted_fldr','weighted_han_hoshi','weighted_reservoir',
                'weighted_sequential','weighted_optimal','weighted_succinct','weighted_two_level','weighted_flat'):
        return frequencies(raw,{0:.1,1:0,2:.3,3:.6})
    if name=='weighted_sorted':return frequencies(raw,{0:0,1:.1,2:.3,3:.6})
    if name in ('weighted_lemire','weighted_division','weighted_debiased','weighted_oneill'):return frequencies(raw,{k:1/7 for k in range(7)})
    if name=='weighted_fenwick':return frequencies(raw,{0:4/7,2:3/7})
    if name=='weighted_floating_multiply':
        def rounded(v):
            step=2**max(0,v.bit_length()-4)
            # Python round gives IEEE's ties-to-even significand convention.
            return round(v/step)*step
        counts=collections.Counter(rounded(5*k)//16 for k in range(16))
        return frequencies(raw,{k:v/16 for k,v in counts.items()})
    if name=='weighted_vose':
        import itertools
        ps={0:.1,2:.3,3:.6}
        return frequencies(raw,{v:math.prod(ps[i] for i in v) for v in itertools.product(ps,repeat=3)})
    if name=='weighted_rational':return frequencies(raw,{0:.5,1:1/3,2:1/6})
    if name in ('weighted_rational_uniform','weighted_dyadic'):
        d=7 if name=='weighted_rational_uniform' else 16
        return frequencies(raw,{(k,d):1/d for k in range(d)})
    if name=='weighted_float':
        pmf={(0,0):1/8}
        pmf.update({(sig,-(z+3)):1/(4*2**(z+1)) for z in range(3) for sig in range(4,8)})
        return frequencies(raw,pmf)
    if name in ('weighted_splitting','weighted_systematic'):
        require(all(len(v)==2 and len(set(v))==2 and set(v)<=set(range(4)) for v in raw),'invalid inclusion sample')
        for i,p in enumerate([.2,.4,.6,.8]):frequencies([i in v for v in raw],{True:p,False:1-p})
        return {'inclusion_probabilities':[.2,.4,.6,.8]}
    if name=='general_discrete_cdf':return frequencies(raw,{0:1/6,1:2/6,2:3/6})
    if name in ('general_pdf','general_metropolis','general_slice','general_slice_stepout'):
        return frequencies(raw,{k:(k+1)/10 for k in range(4)})
    if name=='general_piecewise_constant':return frequencies(raw,{k:p/11 for k,p in enumerate([1,1,3,3,3])})
    if name=='general_piecewise_linear':return frequencies(raw,{k:p/42 for k,p in enumerate([0,4,8,12,9,6,3])})
    if name=='general_refined_coin':return frequencies(raw,{True:1/3,False:2/3})
    if name=='general_incomplete':return frequencies(raw,{0:.25,1:.25,2:.5})
    if name=='general_markov':return frequencies(raw,{0:.25,1:.75})
    if name=='general_perfect':return frequencies(raw,{0:.4,1:.6})
    if name=='general_mh':return frequencies(raw,{0:.2,1:.8})
    if name=='general_markov_trajectory':return frequencies(raw,{(0,0):1/16,(0,1):3/16,(1,0):3/8,(1,1):3/8})
    if name in ('general_gibbs','general_random_scan_gibbs'):
        return frequencies(raw,{0:3/16,1:1/16,2:9/16,3:3/16})
    if name=='general_permutation':
        require(all(v==[9,9] for v in raw),'invariant statistic permutation value')
        return {'deterministic':True}
    if name=='general_walk_path':
        import itertools
        pmf={}
        for signs in itertools.product([-1,1],repeat=3):
            path=[0]
            for sign in signs:path.append(path[-1]+sign)
            pmf[tuple(path)]=1/8
        return frequencies(raw,pmf)
    if name=='general_stopped_sum':return finite_tail(raw,lambda k:poisson_pmf(k,.6))
    if name=='general_stopped_min':return frequencies(raw,{k:((5-k)/5)**3-((4-k)/5)**3 for k in range(5)})
    if name=='general_stopped_max':return frequencies(raw,{k:((k+1)/5)**3-(k/5)**3 for k in range(5)})
    if name=='general_episodes':return frequencies(raw,{(k,3):math.comb(3,k)*.4**k*.6**(3-k) for k in range(4)})
    if name=='discrete_waring':return finite_tail(raw,lambda k:beta_function(4,2+k)/beta_function(3,2))
    if name=='discrete_yule_simon':return finite_tail(raw,lambda k:3*beta_function(k,4),1)
    if name=='discrete_inverse_polya':return finite_tail(raw,lambda k:(k+1)*beta_function(5,2+k)/beta_function(3,2))
    if name=='discrete_cub':
        return frequencies(raw,{k:.6/5+.4*math.comb(4,k-1)*(2/3)**(k-1)*(1/3)**(5-k) for k in range(1,6)})
    if name=='discrete_multipoisson':
        require(all(len(v)==2 and min(v)>=0 for v in raw),'invalid multivariate Poisson')
        for i,rate in enumerate([3,5]):finite_tail([v[i] for v in raw],lambda k:poisson_pmf(k,rate))
        cov=statistics.fmean((v[0]-3)*(v[1]-5) for v in raw)
        require(abs(cov-2)<8*math.sqrt(21/len(raw)),f'Poisson shared covariance {cov}')
        return {'shared_covariance':cov,'expected_covariance':2}
    if name=='discrete_negative_multinomial':
        require(all(len(v)==2 and min(v)>=0 for v in raw),'invalid negative multinomial')
        pmf={(a,b):math.factorial(1+a+b)/(math.factorial(a)*math.factorial(b))* (1/3)**2*(1/6)**a*.5**b
             for a in range(18) for b in range(18)}
        pmf['tail']=1-sum(pmf.values())
        return frequencies([tuple(v) if max(v)<18 else 'tail' for v in raw],pmf)
    if name in ('discrete_multivariate_hypergeometric','discrete_wallenius_multivariate','discrete_fisher_multivariate'):
        counts=[2,3,5];odds=[1,1,1] if name=='discrete_multivariate_hypergeometric' else [1,2,1]
        if name=='discrete_fisher_multivariate':
            ws={}
            for a in range(3):
                for b in range(4):
                    c=4-a-b
                    if 0<=c<=5:ws[a,b,c]=math.comb(2,a)*math.comb(3,b)*math.comb(5,c)*2**b
            total=sum(ws.values());pmf={k:w/total for k,w in ws.items()}
        else:
            states={(0,0,0):1.0}
            for _ in range(4):
                nxt=collections.defaultdict(float)
                for ks,prob in states.items():
                    den=sum((c-k)*w for c,k,w in zip(counts,ks,odds))
                    for i in range(3):
                        if ks[i]<counts[i]:
                            new=list(ks);new[i]+=1
                            nxt[tuple(new)]+=prob*(counts[i]-ks[i])*odds[i]/den
                states=nxt
            pmf=states
        return frequencies(raw,pmf)
    if name=='discrete_pareto':
        factor=-.2*math.log(.6)
        return finite_tail(raw,lambda k:(1+factor*(k-1))**(-5)-(1+factor*k)**(-5),1)
    if name in ('discrete_half_bits','discrete_half_rejection','discrete_binary'):
        n,p=(12,.4) if name=='discrete_binary' else (10,.5)
        return frequencies(raw,{k:math.comb(n,k)*p**k*(1-p)**(n-k) for k in range(n+1)})
    if name in ('discrete_polya','discrete_nb_numerical'):
        return finite_tail(raw,lambda k:math.exp(math.lgamma(k+1.5)-math.lgamma(1.5)-math.lgamma(k+1))* .6**1.5*.4**k)
    if name in ('discrete_beta_nb','discrete_beta_nb_numerical'):
        return finite_tail(raw,lambda k:(k+1)*beta_function(5,2+k)/beta_function(3,2))
    if name=='discrete_beta_binomial':
        return frequencies(raw,{k:math.comb(8,k)*beta_function(3+k,2+8-k)/beta_function(3,2) for k in range(9)})
    if name=='discrete_negative_hypergeometric':
        return frequencies(raw,{k:math.comb(k+1,1)*math.comb(8-k,2)/math.comb(10,4) for k in range(7)})
    if name=='discrete_borel':return finite_tail(raw,lambda k:math.exp(-k/3+(k-1)*math.log(k/3)-math.lgamma(k+1)),1)
    if name=='discrete_logseries':return finite_tail(raw,lambda k:-.4**k/(k*math.log(.6)),1)
    if name=='discrete_zt_poisson':return finite_tail(raw,lambda k:poisson_pmf(k,2)/(1-math.exp(-2)),1)
    if name=='discrete_compound':
        require(all(v%2==0 for v in raw),'constant-jump compound has odd outcome')
        return finite_tail([v//2 for v in raw],lambda k:poisson_pmf(k,1.5))
    if name=='discrete_skellam':
        def pmf(k):
            return sum(poisson_pmf(j+k,3)*poisson_pmf(j,1) for j in range(max(0,-k),70))
        return finite_tail(raw,pmf,-20,21)
    if name=='discrete_polya_aeppli':
        def pmf(n):
            if n==0:return math.exp(-1.5)
            return sum(poisson_pmf(k,1.5)*math.comb(n-1,k-1)*.5**n for k in range(1,n+1))
        return finite_tail(raw,pmf)
    if name=='discrete_neyman':
        return finite_tail(raw,lambda n:sum(poisson_pmf(k,1.5)*poisson_pmf(n,2*k) for k in range(60)))
    if name=='discrete_fisher':
        ws={k:math.comb(3,k)*math.comb(5,4-k)*2**k for k in range(4)}
        return frequencies(raw,{k:w/sum(ws.values()) for k,w in ws.items()})
    if name=='discrete_wallenius':
        states={(0,0):1.0}
        for _ in range(4):
            nxt=collections.defaultdict(float)
            for (a,b),p in states.items():
                den=2*(3-a)+(5-b)
                if a<3:nxt[a+1,b]+=p*2*(3-a)/den
                if b<5:nxt[a,b+1]+=p*(5-b)/den
            states=nxt
        return frequencies(raw,{k:states.get((k,4-k),0) for k in range(4)})
    if name in ('discrete_symmetric','discrete_laplace'):
        rho=.5 if name=='discrete_symmetric' else math.exp(-1)
        return finite_tail(raw,lambda k:(1-rho)/(1+rho)*rho**abs(k),-20,21)
    if name=='discrete_log_uniform':
        pmf={0:.2,1:.2,2:.1,3:.1,**{i:.05 for i in range(4,8)},**{i:.025 for i in range(8,16)}}
        return frequencies(raw,pmf)
    if name=='discrete_zipf':
        total=sum(1/k**2 for k in range(1,6))
        return frequencies(raw,{k:1/(k*k*total) for k in range(1,6)})
    if name=='discrete_zeta':return finite_tail(raw,lambda k:6/(math.pi*k)**2,1,21)
    if name=='discrete_generalized_geometric':return finite_tail(raw,lambda k:2**(-k),1)
    if name=='discrete_sibuya':
        def pmf(k):
            return math.prod(1-2/(2+j) for j in range(1,k))*2/(2+k)
        return finite_tail(raw,pmf,1)
    if name=='discrete_himanshu':return finite_tail(raw,lambda k:.25*.75**k)
    if name in ('discrete_bell','discrete_bell_touchard'):
        rate=(math.exp(.5)-1)*(1.5 if name=='discrete_bell_touchard' else 1)
        def pmf(n):
            if n==0:return math.exp(-rate)
            # General compound-Poisson recurrence with zero-truncated Poisson jumps.
            probs=[math.exp(-rate)]
            for j in range(1,n+1):
                probs.append(rate/j*sum(k*poisson_pmf(k,.5)/(1-math.exp(-.5))*probs[j-k] for k in range(1,j+1)))
            return probs[n]
        return finite_tail(raw,pmf)
    return None


def check(name, raw):
    point = point_oracles.check(name,raw,SCALE)
    if point is not None:return point
    vector = vector_oracles.check(name,raw,SCALE)
    if vector is not None:return vector
    factory = factory_oracles.check(name,raw,SCALE)
    if factory is not None:return factory
    extra=check_extra(name,raw)
    if extra is not None:return extra
    numeric={
      'num_mul':-3.5,'num_div':(-7/3)/1.5,'num_sqrt':math.sqrt(2),
      'num_exp':math.exp(-1.5),'num_log':math.log(1.5),'num_pow':1.5**(7/3),
      'num_sin':math.sin(1.5),'num_cos':math.cos(-1.5),'num_tan':math.tan(1/3),
      'num_atan':math.atan(-7/3),'num_pi':math.pi,'num_cdf':phi(1.5),
      'num_quantile':statistics.NormalDist().inv_cdf(.9),
    }
    if name in numeric:
        xs=[x/SCALE for x in raw]
        error=max(abs(x-numeric[name]) for x in xs)
        require(error<2e-5,f'numerical value {xs[0]} vs {numeric[name]}')
        return {'maximum_absolute_error':error}
    if name=='numeric_coin':return frequencies(raw,{True:.4,False:.6})
    if name in ('normal_box_muller','normal_polar','q_gaussian'):
        require(all(isinstance(v,list) and len(v)==2 for v in raw),'malformed normal pair')
        a=[v[0]/SCALE for v in raw];b=[v[1]/SCALE for v in raw]
        ka=ks(a,lambda x:phi((x-1)/1.5));kb=ks(b,lambda x:phi((x-1)/1.5))
        cov=statistics.fmean((x-1)*(y-1) for x,y in zip(a,b))
        require(abs(cov)<8*2.25/math.sqrt(len(raw)),f'normal coordinates covariance {cov}')
        return {'first':ka,'second':kb,'covariance':cov}
    xs=[x/SCALE for x in raw]
    positive=lambda x:x>=0
    unit=lambda x:0<=x<=1
    cdfs={
      'normal_clt_warped':(phi,lambda x:True),
      'normal_clt_k':(lambda x:irwin_hall(x+6,12),lambda x:-6<=x<=6),
      'gamma_small_shape':(lambda x:gamma_cdf(x,.75,1.5),positive),
      'power_function':(lambda x:(x/2)**2,lambda x:0<=x<=2),
      'stacy':(lambda x:gamma_cdf((x/2)**2,2),positive),
      'amoroso':(lambda x:gamma_cdf(((x-1)/2)**2,2),lambda x:x>=1),
      'pearson_vi':(lambda x:beta_cdf(x/(1+x),2,3),positive),
      'singh_maddala':(lambda x:1-(1+x*x)**(-3),positive),
      'dagum':(lambda x:(x*x/(1+x*x))**3,positive),
      'log_logistic':(lambda x:x*x/(1+x*x),positive),
      'minimum_uniform':(lambda x:1-(1-x)**3,unit),
      'maximum_uniform':(lambda x:x**3,unit),
      'hypoexponential':(lambda x:(1-math.exp(-x))**2,positive),
      'hyperexponential':(lambda x:1-.25*math.exp(-x)-.75*math.exp(-2*x),positive),
      'numerical_piecewise_linear':(lambda x:4*x*x if x<.25 else 1-(1-x)**2/.75,unit),
      'numerical_piecewise_constant':(lambda x:x/2.5 if x<.25 else .1+3*(x-.25)/2.5,unit),
      'sine_power':(lambda x:(1-math.cos(x))/2,lambda x:0<=x<=math.pi),
      'numeric_uniform':(lambda x:x,unit),
      'uniform_range':(lambda x:(x+2)/5,lambda x:-2<=x<=3),
      'exponential_rate':(lambda x:-math.expm1(-1.5*x),positive),
      'normal':(lambda x:phi((x-1)/1.5),lambda x:True),
      'normal_ratio':(lambda x:phi((x-1)/1.5),lambda x:True),
      'normal_inversion':(lambda x:phi((x-1)/1.5),lambda x:True),
      'normal_clt':(lambda x:irwin_hall(x+6,12),lambda x:-6<=x<=6),
      'gamma':(lambda x:gamma_cdf(x,2.5,1.5),positive),
      'gamma_small':(lambda x:gamma_cdf(x,.75,1.5),positive),
      'beta':(lambda x:beta_cdf(x,2,3),unit),
      'beta_small':(lambda x:beta_cdf(x,.75,1.25),unit),
      'lognormal':(lambda x:phi(math.log(x)/.5) if x>0 else 0,positive),
      'laplace':(lambda x:.5*math.exp((x-1)/2) if x<1 else 1-.5*math.exp(-(x-1)/2),lambda x:True),
      'logistic':(lambda x:1/(1+math.exp(-x)),lambda x:True),
      'cauchy':(lambda x:.5+math.atan(x)/math.pi,lambda x:True),
      'cauchy_disk':(lambda x:.5+math.atan(x)/math.pi,lambda x:True),
      'chi_squared':(lambda x:gamma_cdf(x,1.5,.5),positive),
      'noncentral_chi_squared':(poisson_mix(lambda x,k:gamma_cdf(x,1.5+k,.5),1),positive),
      'student_t':(lambda x:.5*beta_cdf(5/(5+x*x),2.5,.5) if x<0 else 1-.5*beta_cdf(5/(5+x*x),2.5,.5),lambda x:True),
      'fisher_f':(lambda x:beta_cdf(4*x/(4*x+8),2,4),positive),
      'inverse_gamma':(lambda x:1-gamma_cdf(2/x,3) if x>0 else 0,positive),
      'inverse_gaussian':(lambda x:phi(math.sqrt(3/x)*(x/2-1))+math.exp(3)*phi(-math.sqrt(3/x)*(x/2+1)) if x>0 else 0,positive),
      'weibull':(lambda x:-math.expm1(-(x/2)**1.5),positive),
      'pareto':(lambda x:1-(2/x)**3,lambda x:x>=2),
      'rayleigh':(lambda x:-math.expm1(-x*x/8),positive),
      'gumbel':(lambda x:math.exp(-math.exp(-(x-1)/2)),lambda x:True),
      'gev':(lambda x:math.exp(-(1+.25*x)**(-4)),lambda x:x>-4),
      'frechet':(lambda x:math.exp(-((x-1)/2)**(-3)) if x>1 else 0,lambda x:x>=1),
      'triangular':(lambda x:4*x*x if x<.25 else 1-(1-x)**2/.75,unit),
      'triangular_uniforms':(lambda x:2*x*x if x<.5 else 1-2*(1-x)**2,unit),
      'kumaraswamy':(lambda x:1-(1-x*x)**3,unit),
      'beta_prime':(lambda x:beta_cdf(x/(1+x),2,3),positive),
      'beta_pert':(lambda x:beta_cdf(x,2,4),unit),
      'noncentral_beta':(poisson_mix(lambda x,k:beta_cdf(x,2+k,3),1),unit),
      'half_normal':(lambda x:2*phi(x/2)-1,positive),
      'chi':(lambda x:gamma_cdf(x*x,1.5,.5),positive),
      'inverse_chi_squared':(lambda x:1-gamma_cdf(5/x,2.5,.5) if x>0 else 0,positive),
      'levy':(lambda x:math.erfc(math.sqrt(1/(x-1))) if x>1 else 0,lambda x:x>=1),
      'maxwell':(lambda x:gamma_cdf(x*x/8,1.5),positive),
      'wigner':(lambda x:.5+(x*math.sqrt(max(0,1-x*x))+math.asin(max(-1,min(1,x))))/math.pi,lambda x:-1<=x<=1),
      'parabolic':(lambda x:beta_cdf(x,2,2),unit),
      'arcsine':(lambda x:2/math.pi*math.asin(math.sqrt(x)),unit),
      'generalized_normal':(lambda x:phi(x*math.sqrt(2)),lambda x:True),
      'generalized_gamma':(lambda x:gamma_cdf(x*x,2),positive),
      'generalized_inverse_gamma':(lambda x:1-gamma_cdf(1/(x*x),2) if x>0 else 0,positive),
      'birnbaum_saunders':(lambda x:phi(math.sqrt(x)-1/math.sqrt(x)) if x>0 else 0,positive),
      'tukey_lambda':(lambda x:(x+1)/2,lambda x:-1<=x<=1),
      'generalized_tukey_lambda':(lambda x:(x+1)/5,lambda x:-1<=x<=4),
      'power_law_negative':(lambda x:2*(1-1/x),lambda x:1<=x<=2),
      'power_law':(lambda x:(x*x-1)/3,lambda x:1<=x<=2),
      'power_distribution':(lambda x:(2*x)**2,lambda x:0<=x<=.5),
      'logarithmic_product':(lambda x:x-x*math.log(x) if x>0 else 0,unit),
      'double_logarithmic':(lambda x:.5*(1-((1-2*x)-(1-2*x)*math.log(1-2*x))) if x<.5 else .5+.5*((2*x-1)-(2*x-1)*math.log(2*x-1)) if x>.5 else .5,unit),
      'bates':(lambda x:irwin_hall(3*x,3),unit),
      'skew_normal_extremes':(lambda x:phi(x*math.sqrt(2)),lambda x:True),
      'generalized_skew_normal':(phi,lambda x:True),
      'moyal':(lambda x:math.erfc(math.exp(-x/2)/math.sqrt(2)),lambda x:True),
      'power_normal':(lambda x:1-(1-phi(x))**2,lambda x:True),
      'power_lognormal':(lambda x:1-(1-phi(math.log(x)))**2 if x>0 else 0,positive),
    }
    if name in cdfs:return ks(xs,*cdfs[name])
    if name in ('skew_normal','skew_normal_conditional'):
        mean=2/math.sqrt(5)*math.sqrt(2/math.pi);variance=1-8/(5*math.pi)
        actual=statistics.fmean(xs)
        require(abs(actual-mean)<8*math.sqrt(variance/len(xs)),f'skew-normal mean {actual}')
        return {'mean':actual,'expected_mean':mean,'variance':statistics.pvariance(xs)}
    if name=='twin_t':
        require(all(math.isfinite(x) for x in xs),'nonfinite twin-t')
        return frequencies([x<0 for x in xs],{True:.5,False:.5})
    raise AssertionError('missing oracle for '+name)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--count',type=int,default=1200)
    p.add_argument('--seed',type=int,default=20261106)
    p.add_argument('--case',action='append')
    p.add_argument('--prefix',action='append',help='limit to case-name prefixes')
    p.add_argument('--report',type=Path,default=ROOT/'tests/wide-results.json')
    p.add_argument('--merge-report',action='store_true',help='retain unchanged prior cases and append a transparent rerun batch')
    args=p.parse_args()
    names=json.loads(subprocess.check_output([str(EXE),'--list'],text=True))
    require(len(set(names))==len(names),'duplicate fixture names')
    require(args.count>0,'sample count must be positive')
    if args.case:
        require(set(args.case)<=set(names),'unknown requested case')
        names=[n for n in names if n in args.case]
    if args.prefix:names=[n for n in names if any(n.startswith(p) for p in args.prefix)]
    require(bool(names),'no selected fixture names')
    previous=json.loads(args.report.read_text()) if args.merge_report and args.report.exists() else None
    previous_seeds={r['case']:r['seed'] for r in previous['results']} if previous else {}
    results=[];start=time.monotonic()
    for i,name in enumerate(names):
        seed=previous_seeds.get(name,args.seed+i*104729);t=time.monotonic()
        try:
            if name.startswith('invalid_'):
                r=subprocess.run([str(EXE),name,'1',str(seed),'env'],capture_output=True,text=True,timeout=30)
                require(r.returncode!=0 and 'stuck: fail' in r.stderr,'expected explicit fail')
                details={'samples':0,'expected_failure':True}
            else:
                n=1 if name.startswith('num_') else min(args.count,400) if name in ('normal_inversion','power_normal','power_lognormal') else args.count
                n=min(n,factory_oracles.COUNTS.get(name,n),point_oracles.COUNTS.get(name,n))
                if name.startswith("psrn_"):n=min(n,128)
                if name in ("psrn_rational_arithmetic","psrn_less_rational"):n=1
                xs=draw(name,n,seed)
                details={'samples':n,**check(name,xs)}
                if factory_oracles.COUNTS.get(name,0)!=1:
                    require(draw(name,3,seed+1)==draw(name,3,seed+1,'subst'),
                            'seeded environment/substitution disagreement')
                    details['differential_samples']=6
                else:details['differential_samples']=0
            results.append({'case':name,'passed':True,'seed':seed,'seconds':time.monotonic()-t,**details})
            print(f'PASS {name} ({time.monotonic()-t:.2f}s)',flush=True)
        except (AssertionError,ValueError,subprocess.TimeoutExpired,OverflowError,ZeroDivisionError,TypeError,IndexError,KeyError) as e:
            results.append({'case':name,'passed':False,'seed':seed,'error':str(e),'seconds':time.monotonic()-t})
            print(f'FAIL {name}: {e}',flush=True)
    batch={'cases':len(results),'passed':sum(r['passed'] for r in results),
           'failed':sum(not r['passed'] for r in results),'seconds':time.monotonic()-start,
           'total_samples':sum(r.get('samples',0) for r in results),
           'seed':args.seed,'count':args.count,
           'failures':{r['case']:r.get('error','') for r in results if not r['passed']}}
    batches=[]
    if previous:
        batches=previous.get('batches',[])
        if not batches:
            batches=[{k:previous[k] for k in ['passed','failed','seconds','total_samples','seed','count']}]
            batches[0]['cases']=len(previous['results'])
            batches[0]['failures']={r['case']:r.get('error','') for r in previous['results'] if not r['passed']}
        merged={r['case']:r for r in previous['results']}
        merged.update({r['case']:r for r in results})
        results=list(merged.values())
    batches.append(batch)
    report={'scale':SCALE,'per_bound_alpha':ALPHA,'grid_cdf_allowance':.002,
            'count':args.count,'seed':args.seed,'passed':sum(r['passed'] for r in results),
            'failed':sum(not r['passed'] for r in results),
            'seconds':sum(r.get('seconds',0) for r in results),
            'last_batch_seconds':batch['seconds'],
            'validation_elapsed_seconds':sum(b.get('seconds',0) for b in batches),
            'total_samples':sum(r.get('samples',0) for r in results),'results':results,'batches':batches}
    if previous and 'regressions' in previous:
        report['regressions']=previous['regressions']
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(f"{report['passed']}/{len(results)} passed; {report['total_samples']} primary draws")
    raise SystemExit(bool(report['failed']))

if __name__=='__main__':main()
