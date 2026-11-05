"""Independent checks for point-selection and supplied-data-model samplers.

Finite deterministic prefixes are checked against exact source definitions.
Randomized point sets are checked for stratification, dimension, support and
hard-core spacing, not incorrectly tested as iid point vectors.
"""
import collections
import itertools
import math
import statistics

COUNTS = {name: 1 for name in [
    'point_vdc_rational','point_vdc_prefix','point_halton_prefix','point_scrambled',
    'point_shift','point_baker','point_roberts','point_sobol_prefix','point_lattice',
    'point_lfsr_grid8','model_regression_zero_error',
]}
COUNTS.update({'point_best_candidate': 200, 'point_farthest': 200,
               'point_poisson_disk_grid32': 200, 'point_stratified_box': 300,
               'point_latin3': 300})
LOG = math.log(2/1e-9)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def freeze(value):
    return tuple(map(freeze,value)) if isinstance(value,list) else value


def frequencies(raw, pmf):
    counts=collections.Counter(map(freeze,raw))
    require(set(counts)<=set(pmf),'out-of-support result')
    require(abs(sum(pmf.values())-1)<1e-9,'oracle PMF not normalized')
    for x,p in pmf.items():
        bound=math.sqrt(2*len(raw)*p*(1-p)*LOG)+2*LOG/3
        require(abs(counts[x]-len(raw)*p)<=bound,'frequency mismatch '+str(x))
    return {'categories':len(pmf)}


def cdf_check(values,cdf,allowance=1e-5):
    require(all(math.isfinite(x) for x in values),'nonfinite sample')
    n=len(values)
    d=max(max((i+1)/n-cdf(x),cdf(x)-i/n) for i,x in enumerate(sorted(values)))
    limit=math.sqrt(LOG/(2*n))+allowance
    require(d<=limit,f'CDF discrepancy {d} > {limit}')
    return {'ks':d,'ks_bound':limit,'mean':statistics.fmean(values)}


def radical_inverse(base,index):
    numerator,denominator=0,1
    while index:
        numerator=numerator*base+index%base
        denominator*=base
        index//=base
    return numerator,denominator


def point_shape(points,count,dimension,scale):
    require(isinstance(points,list) and len(points)==count,'wrong point count')
    require(all(isinstance(p,list) and len(p)==dimension and
                all(type(x) is int and 0<=x<scale for x in p) for p in points),
            'wrong point shape/support')


def check(name,raw,scale):
    if not name.startswith(('point_','model_')):
        return None
    deterministic={
      'point_vdc_rational':[3,4],
      'point_vdc_prefix':[scale*n//d for n,d in (radical_inverse(2,i) for i in range(8))],
      'point_halton_prefix':[[scale*n//d for n,d in (radical_inverse(b,i) for b in [2,3])]
                              for i in range(8)],
      'point_scrambled':7*scale//8,
      'point_shift':[3*scale//4,scale//4],
      'point_baker':[0,scale//2,scale,scale//2,0],
      'point_sobol_prefix':[[scale*x//8,scale*y//8] for x,y in
                           [(0,0),(4,4),(6,2),(2,6),(3,3),(7,7),(5,1),(1,5)]],
      'point_lattice':[scale*92717//262139,scale*185434//262139],
      'point_lfsr_grid8':[[1,4,2,5,6,7,3],1],
      'model_regression_zero_error':5*scale//2,
    }
    if name in deterministic:
        require(all(x==deterministic[name] for x in raw),'deterministic prefix mismatch')
        return {'deterministic':True}
    if name=='point_roberts':
        phi=1.324717957244746
        expected=[(.5+phi**(-i))%1 for i in [1,2]]
        require(all(len(v)==2 and all(abs(x/scale-y)<=12/scale
                    for x,y in zip(v,expected)) for v in raw),'Roberts root/recurrence')
        return {'deterministic':True,'numerical_allowance':12/scale}
    if name in ('point_stratified','point_latin1'):
        for xs in raw:
            require(len(xs)==4 and all(type(x) is int and 0<=x<scale for x in xs),'stratum shape')
            require(sorted(4*x//scale for x in xs)==list(range(4)),'one point per stratum lost')
            if name=='point_stratified':
                require([4*x//scale for x in xs]==list(range(4)),'stratum order lost')
        jitter=[(4*x)%scale/scale for xs in raw for x in xs]
        return cdf_check(jitter,lambda x:min(1,max(0,x)))
    if name=='point_latin3':
        for points in raw:
            point_shape(points,4,3,scale)
            for j in range(3):
                require(sorted(4*p[j]//scale for p in points)==list(range(4)),
                        'Latin hypercube marginal strata lost')
        return {'point_sets':len(raw),'dimension':3}
    if name=='point_stratified_box':
        for points in raw:
            point_shape(points,8,2,scale)
            counts=collections.Counter((2*p[0]//scale,2*p[1]//scale) for p in points)
            require(counts=={k:2 for k in itertools.product(range(2),repeat=2)},'box stratum counts')
        return {'point_sets':len(raw),'dimension':2}
    if name=='point_best_candidate':
        for points in raw: point_shape(points,6,2,scale)
        means=[statistics.fmean(x/scale for p in points for x in p) for points in raw]
        require(abs(statistics.fmean(means)-.5)<8*math.sqrt(.25/len(means))+.002,
                'best-candidate symmetry/mean')
        return {'point_sets':len(raw),'mean':statistics.fmean(means)}
    if name=='point_farthest':
        for points in raw:
            require(sorted(p[0] for p in points)==[0,2,5,9] and all(len(p)==1 for p in points),
                    'farthest traversal changed pool')
            seen=[points[0][0]]
            remaining={0,2,5,9}-set(seen)
            for point in points[1:]:
                distance=lambda x:min((x-y)**2 for y in seen)
                require(distance(point[0])==max(map(distance,remaining)),'not farthest remaining point')
                seen.append(point[0]);remaining.remove(point[0])
        return {'point_sets':len(raw)}
    if name=='point_poisson_disk_grid32':
        completed=0
        for pair in raw:
            require(isinstance(pair,list) and len(pair)==2 and type(pair[1]) is bool,'completion flag')
            points,complete=pair
            point_shape(points,len(points),2,32)
            require(len(points)<=8 and complete==(len(points)==8),'short packing mislabeled complete')
            require(all(sum((x-y)**2 for x,y in zip(a,b))>=25
                        for a,b in itertools.combinations(points,2)),'Poisson-disk spacing violated')
            completed+=complete
        return {'point_sets':len(raw),'completed':completed}
    if name=='model_bootstrap':
        require(all(len(v)==2 and all(len(row)==3 and set(row)<={0,1,2} for row in v) for v in raw),
                'bootstrap shape/support')
        for j in range(2):
            for i in range(3): frequencies([v[j][i] for v in raw],{0:1/3,1:1/3,2:1/3})
        return {'replicates_per_draw':2}
    if name=='model_permutations':
        require(all(len(v)==2 and all(sorted(row)==[0,1,2] for row in v) for v in raw),'bad permutation')
        pmf={x:1/6 for x in itertools.permutations(range(3))}
        for j in range(2): frequencies([v[j] for v in raw],pmf)
        return {'replicates_per_draw':2}
    if name=='model_grouped_permutation':
        require(all([len(g) for g in v]==[2,1,3] and sorted(x for g in v for x in g)==list(range(6))
                    for v in raw),'regrouping changed sample/group sizes')
        return frequencies([v[0] for v in raw],{x:1/30 for x in itertools.permutations(range(6),2)})
    if name=='model_histogram_grid':
        return frequencies(raw,{0:1/8,1:1/8,2:1/4,3:1/4,4:1/4})
    if name=='model_kde':
        xs=[x/scale for x in raw]
        require(all(-3<=x<=-1 or 1<=x<=3 for x in xs),'KDE support')
        uniform=lambda x,a,b:min(1,max(0,(x-a)/(b-a)))
        return cdf_check(xs,lambda x:.5*uniform(x,-3,-1)+.5*uniform(x,1,3))
    if name=='model_kde_vector':
        require(all(len(v)==2 and all(.75<=abs(x/scale)<=1.25 for x in v)
                    and v[0]*v[1]>0 for v in raw),'KDE center identity/correlated signs lost')
        cov=statistics.fmean(v[0]*v[1]/scale**2 for v in raw)
        require(abs(cov-1)<8*math.sqrt(2.5/len(raw))+.002,'KDE latent covariance')
        return {'covariance':cov}
    normal=statistics.NormalDist()
    if name=='model_gaussian_kde':
        return cdf_check([x/scale for x in raw],normal.cdf,.003)
    if name=='model_gaussian_mixture':
        return cdf_check([x/scale for x in raw],lambda x:.25*normal.cdf(x+1)+.75*normal.cdf(2*(x-2)),.003)
    if name=='model_regression':
        return cdf_check([x/scale for x in raw],lambda x:normal.cdf((x-2.5)/.5),.003)
    if name=='model_generative':return frequencies(raw,{0:1/3,1:1/3,4:1/3})
    if name=='model_classified':return frequencies(raw,{(0,10):.25,(1,20):.75})
    if name=='model_stochastic_bootstrap':
        return frequencies(raw,{(0,0):.25,(scale,0):.25,(0,scale):.25,(scale,scale):.25})
    if name=='model_stochastic_interpolation':
        require(all(len(v)==2 and all(-1-1e-4<=x/scale<=2+1e-4 for x in v) for v in raw),
                'stochastic interpolation shape/support')
        def cdf(x):
            z=(x+1)/.75
            if z<=0:return 0.0
            if z>=4:return 1.0
            return sum((-1)**k*math.comb(4,k)*max(0,z-k)**4 for k in range(5))/24
        result={}
        for j in range(2):result['coordinate_'+str(j)]=cdf_check([v[j]/scale for v in raw],cdf,.003)
        return result
    raise AssertionError('missing point/model oracle '+name)
