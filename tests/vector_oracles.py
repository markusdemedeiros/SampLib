"""Independent analytic checks for vector, rare-family, and lazy-real fixtures.

Inputs are decoded interpreter outputs. Numerical outputs use the supplied fixed
point scale; lazy finite observations deliberately use a separate 256-cell grid.
Every quantitative check has conservative tolerances; these are implementation tests.
"""
import math
import statistics

LOG = math.log(2 / 1e-9)


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def cdf_check(xs, cdf, support=lambda x: True, allowance=.003):
    require(all(math.isfinite(x) and support(x) for x in xs), 'nonfinite/out-of-support sample')
    n = len(xs)
    ys = sorted(xs)
    d = max(max((i+1)/n-cdf(x), cdf(x)-i/n) for i,x in enumerate(ys))
    bound = math.sqrt(LOG/(2*n)) + allowance
    require(d <= bound, f'CDF discrepancy {d:.6g} > {bound:.6g}')
    return {'ks': d, 'ks_bound': bound, 'mean': statistics.fmean(xs)}


def mean_check(xs, mean, variance, allowance=.003):
    actual = statistics.fmean(xs)
    limit = 8*math.sqrt(variance/len(xs)) + allowance
    require(abs(actual-mean) <= limit, f'mean {actual:.6g} != {mean:.6g} (limit {limit:.6g})')
    return actual


def probability(xs, predicate, p):
    observed = sum(bool(predicate(x)) for x in xs)
    bound = math.sqrt(2*len(xs)*p*(1-p)*LOG) + 2*LOG/3
    require(abs(observed-len(xs)*p) <= bound, f'event count {observed} != {len(xs)*p:.4g}')
    return observed/len(xs)


def vectors(raw, scale, dimensions):
    require(all(isinstance(v,list) and len(v)==dimensions and
                all(type(x) is int for x in v) for v in raw), 'invalid vector result shape')
    return [[x/scale for x in v] for v in raw]


def gamma_cdf_integer(x, shape, rate=1):
    if x <= 0: return 0.0
    return 1-math.exp(-rate*x)*sum((rate*x)**k/math.factorial(k) for k in range(shape))


def beta_cdf_integer(x, a, b):
    if x <= 0: return 0.0
    if x >= 1: return 1.0
    n = a+b-1
    return sum(math.comb(n,k)*x**k*(1-x)**(n-k) for k in range(a,n+1))


def student5_cdf(x):
    a = math.atan(x/math.sqrt(5))
    return .5 + (3*a/8 + math.sin(2*a)/4 + math.sin(4*a)/32)/(3*math.pi/8)


def tulap_cdf(x, b=.5):
    n = math.floor(x+.5)
    fraction = x-n+.5
    before = b**(1-n)/(1+b) if n <= 0 else 1-b**n/(1+b)
    return before + fraction*(1-b)/(1+b)*b**abs(n)


def check(name, raw_values, scale):
    if not name.startswith(('vector_','special_','psrn_')):
        return None
    if name == 'psrn_less_rational':
        require(all(x is True for x in raw_values), 'incorrect exact rational comparison')
        return {'deterministic': True}
    if name == 'psrn_rational_arithmetic':
        require(all(x==187 and type(x) is int for x in raw_values), 'incorrect rational interval arithmetic')
        return {'deterministic': True}
    if name == 'psrn_reread':
        require(all(isinstance(v,list) and len(v)==2 and v[0]==v[1] for v in raw_values),
                'lazy observation changed its latent sample')
        return cdf_check([v[0]/256 for v in raw_values], lambda x: min(1,max(0,x)),
                         lambda x: 0<=x<1, .01)
    if name.startswith('psrn_'):
        require(all(type(x) is int for x in raw_values), 'invalid lazy scalar observation')
        xs = [x/256 for x in raw_values]
        if name == 'psrn_uniform':
            return cdf_check(xs,lambda x:min(1,max(0,x)),lambda x:0<=x<1,.01)
        if name == 'psrn_shared_square':
            return cdf_check(xs,lambda x:math.sqrt(max(0,x)),lambda x:0<=x<1,.01)
        if name == 'psrn_independent_product':
            return cdf_check(xs,lambda x:0 if x<=0 else x*(1-math.log(x)),lambda x:0<=x<1,.025)
        if name == 'psrn_sum':
            return cdf_check(xs,lambda x:x*x/2 if x<=1 else 1-(2-x)**2/2,lambda x:0<=x<2,.01)
        if name == 'psrn_beta':
            return cdf_check(xs,lambda x:beta_cdf_integer(x,2,3),lambda x:0<=x<1,.01)
        if name == 'psrn_beta_fractional':
            # Exact latent beta(3/2,5/4); first two moments do not use its implementation.
            require(all(0<=x<1 for x in xs),'invalid beta support')
            mean=1.5/2.75;variance=1.5*1.25/(2.75**2*3.75)
            return {'mean':mean_check(xs,mean,variance,.01)}
        if name == 'psrn_exponential':
            return cdf_check(xs,lambda x:-math.expm1(-2*x),lambda x:x>=0,.01)
        if name == 'psrn_gamma':
            return cdf_check(xs,lambda x:gamma_cdf_integer(x,2,2),lambda x:x>=0,.01)
        if name == 'psrn_epanechnikov':
            return cdf_check(xs,lambda x:.5+.75*x-.25*x**3,lambda x:-1<=x<1,.01)
        if name == 'psrn_cauchy':
            return cdf_check(xs,lambda x:.5+math.atan(x)/math.pi,allowance=.01)
        raise AssertionError('missing PSRN oracle '+name)
    if name.startswith('special_'):
        if name == 'special_rectellipse':
            xs=vectors(raw_values,scale,2)
            require(all(abs(x*x+(y/2)**2-1)<=.001 or x*x+(y/2)**2<1 for x,y in xs),
                    'outside ellipse')
            cdf_check([x for x,y in xs],lambda x:.5+(x*math.sqrt(max(0,1-x*x))+math.asin(max(-1,min(1,x))))/math.pi,
                      lambda x:abs(x)<=1.001)
            return {'mean_x':mean_check([x for x,y in xs],0,.25),
                    'mean_y':mean_check([y for x,y in xs],0,1)}
        require(all(type(x) is int for x in raw_values),'invalid scalar numerical result')
        xs=[x/scale for x in raw_values]
        mixtures={
          'special_lindley':(2/3,1,2,1), 'special_garima':(3/4,1,2,1),
          'special_i_garima':(4/5,1,2,1), 'special_weighted_exp_gamma':(2/3,2,3,1),
          'special_xgamma':(2/3,1,3,1), 'special_mirra':(4/5,1,3,1),
          'special_sushila':(2/3,1,2,2), 'special_xlindley':(8/9,1,2,1),
        }
        if name in mixtures:
            p,a,b,stretch=mixtures[name]
            return cdf_check(xs,lambda x:p*gamma_cdf_integer(x/stretch,a,2)+(1-p)*gamma_cdf_integer(x/stretch,b,2),
                             lambda x:x>=0)
        if name=='special_sech':
            return cdf_check(xs,lambda x:2/math.pi*math.atan(math.exp(x)))
        if name=='special_epanechnikov':
            return cdf_check(xs,lambda x:.5+.75*x-.25*x**3,lambda x:-1<=x<=1)
        if name=='special_ratio_uniforms':
            return cdf_check(xs,lambda x:x/2 if x<=1 else 1-1/(2*x),lambda x:x>=0)
        if name=='special_reciprocal_uniform':
            return cdf_check(xs,lambda x:1-1/x,lambda x:x>=1)
        if name=='special_uniform_odds':
            return cdf_check(xs,lambda x:x/(1+x),lambda x:x>=0)
        if name=='special_arccosine':
            return cdf_check(xs,lambda x:1-math.cos(math.pi*x/2),lambda x:0<=x<=1)
        if name=='special_exp_log_rate':
            return cdf_check(xs,lambda x:-math.expm1(-math.log(2)*x),lambda x:x>=0)
        if name=='special_tulap': return cdf_check(xs,tulap_cdf)
        if name=='special_tulap_trimmed':
            return cdf_check(xs,lambda x:max(0,min(1,(tulap_cdf(x)-.25)/.5)))
        if name=='special_continuous_bernoulli':
            return cdf_check(xs,lambda x:(3**x-1)/2,lambda x:0<=x<=1)
        if name=='special_lomax':
            return cdf_check(xs,lambda x:1-(1+x)**-3,lambda x:x>=0)
        if name=='special_topp_leone':
            return cdf_check(xs,lambda x:(2*x-x*x)**2,lambda x:0<=x<=1)
        if name=='special_marshall_olkin':
            return cdf_check(xs,lambda x:.5*x/(1-.5*x),lambda x:0<=x<=1)
        if name=='special_unit_lindley':
            return cdf_check(xs,lambda x:2/3*gamma_cdf_integer(x/(1-x),1,2)+1/3*gamma_cdf_integer(x/(1-x),2,2),
                             lambda x:0<=x<1)
        raise AssertionError('missing specialized oracle '+name)
    # Vector families.
    if name in ('vector_phase_type','vector_erlang_phase_type','vector_stable_cauchy',
                'vector_stable_normal','vector_linnik','vector_mittag_leffler','vector_von_mises_uniform',
                'vector_von_mises'):
        require(all(type(x) is int for x in raw_values),'invalid scalar result')
        xs=[x/scale for x in raw_values]
        if name=='vector_phase_type': return cdf_check(xs,lambda x:-math.expm1(-x),lambda x:x>=0)
        if name=='vector_erlang_phase_type': return cdf_check(xs,lambda x:gamma_cdf_integer(x,2),lambda x:x>=0)
        if name=='vector_stable_cauchy': return cdf_check(xs,lambda x:.5+math.atan(x)/math.pi)
        if name=='vector_stable_normal': return cdf_check(xs,lambda x:.5*math.erfc(-x/2))
        if name=='vector_linnik': return cdf_check(xs,lambda x:.5*math.exp(x) if x<0 else 1-.5*math.exp(-x))
        if name=='vector_mittag_leffler': return cdf_check(xs,lambda x:-math.expm1(-x),lambda x:x>=0)
        if name=='vector_von_mises_uniform':
            return cdf_check(xs,lambda x:(x+math.pi)/(2*math.pi),lambda x:abs(x)<=math.pi+.001)
        require(all(abs(x)<=math.pi+.001 for x in xs),'von Mises angle support')
        return {'cosine_mean':mean_check([math.cos(x) for x in xs],.697774657964008,.2),
                'sine_mean':mean_check([math.sin(x) for x in xs],0,.4)}
    dim=3 if name in ('vector_dirichlet','vector_partition','vector_sphere','vector_ball',
                      'vector_shell','vector_hypercube','vector_cone','vector_cylinder','vector_upper_copula') else 2
    vs=vectors(raw_values,scale,dim)
    if name in ('vector_normal','vector_binormal','vector_binormal_endpoint'):
        mean_y=1 if name=='vector_normal' else 0
        var_y=2 if name=='vector_normal' else 1
        xs=[v[0] for v in vs];ys=[v[1]-mean_y for v in vs]
        cdf_check(xs,lambda x:.5*math.erfc(-x/math.sqrt(2)))
        cdf_check(ys,lambda x:.5*math.erfc(-x/math.sqrt(2*var_y)))
        if name=='vector_binormal_endpoint':
            require(all(x==y for x,y in vs),'rho=1 did not preserve exact common coordinate')
        cov=statistics.fmean(x*y for x,y in zip(xs,ys))
        expected=1 if name=='vector_binormal_endpoint' else .5
        require(abs(cov-expected)<8*math.sqrt((var_y+expected**2)/len(vs))+.01,'wrong normal covariance')
        return {'covariance':cov,'expected_covariance':expected}
    if name in ('vector_dirichlet','vector_partition'):
        total=1 if name=='vector_dirichlet' else 2
        require(all(all(x>=0 for x in v) and abs(sum(v)-total)<1/scale for v in vs),
                'Dirichlet/partition does not conserve total')
        shapes=[1,2,3] if name=='vector_dirichlet' else [1,1,1]
        for j,a in enumerate(shapes):
            cdf_check([v[j]/total for v in vs],lambda x,a=a:beta_cdf_integer(x,a,sum(shapes)-a),lambda x:0<=x<=1)
        return {'coordinate_means':[statistics.fmean(v[j] for v in vs) for j in range(3)]}
    if name in ('vector_sphere','vector_ball','vector_shell'):
        radii=[math.sqrt(sum(x*x for x in v)) for v in vs]
        if name=='vector_sphere':require(all(abs(r-1)<.001 for r in radii),'sphere radius')
        elif name=='vector_ball':cdf_check(radii,lambda r:r**3,lambda r:0<=r<=1.001)
        else:cdf_check(radii,lambda r:(r**3-1)/7,lambda r:.999<=r<=2.001)
        for j in range(3):mean_check([v[j] for v in vs],0,4/3)
        return {'mean_radius':statistics.fmean(radii)}
    if name in ('vector_box','vector_hypercube'):
        for j in range(dim):
            lo,hi=(-1,1) if name=='vector_hypercube' or j==0 else (0,2)
            cdf_check([v[j] for v in vs],lambda x,lo=lo,hi=hi:(x-lo)/(hi-lo),lambda x,lo=lo,hi=hi:lo<=x<=hi)
        return {'coordinate_means':[statistics.fmean(v[j] for v in vs) for j in range(dim)]}
    if name in ('vector_cone','vector_cylinder'):
        require(all(0<=z<=2.001 and x*x+y*y<=(z/2)**2+.003 if name=='vector_cone'
                    else 0<=z<=2.001 and x*x+y*y<=1.003 for x,y,z in vs),'cone/cylinder support')
        cdf_check([v[2] for v in vs],lambda z:(z/2)**3 if name=='vector_cone' else z/2)
        return {'mean_z':statistics.fmean(v[2] for v in vs)}
    if name in ('vector_circle','vector_ellipsoid'):
        require(all(abs(x*x+(y/(2 if name=='vector_ellipsoid' else 1))**2-1)<.002 for x,y in vs),
                'surface constraint')
        return {'mean_x':mean_check([v[0] for v in vs],0,1),
                'mean_y':mean_check([v[1] for v in vs],0,4)}
    if name=='vector_latlon':
        cdf_check([math.sin(v[0]) for v in vs],lambda x:(x+1)/2,lambda x:abs(x)<=1)
        return cdf_check([v[1] for v in vs],lambda x:(x+math.pi)/(2*math.pi),lambda x:abs(x)<=math.pi+.001)
    if name in ('vector_simplex','vector_triangle'):
        require(all(x>=0 and y>=0 and x+y<=1.001 for x,y in vs),'simplex support')
        for j in range(2):cdf_check([v[j] for v in vs],lambda x:2*x-x*x,lambda x:0<=x<=1)
        return {'mean_x':statistics.fmean(v[0] for v in vs)}
    if name in ('vector_gaussian_copula','vector_product_copula','vector_upper_copula',
                'vector_lower_copula','vector_clayton','vector_gumbel_copula','vector_exchangeable_fgm'):
        for j in range(dim):cdf_check([v[j] for v in vs],lambda x:x,lambda x:0<=x<=1)
        if name=='vector_upper_copula':require(all(v[0]==v[1]==v[2] for v in vs),'upper copula coupling')
        if name=='vector_lower_copula':require(all(abs(sum(v)-1)<1/scale for v in vs),'lower copula coupling')
        expected={'vector_product_copula':.25,'vector_clayton':1/3,
                  'vector_gumbel_copula':.5**math.sqrt(2),
                  'vector_exchangeable_fgm':.3125}.get(name)
        result={}
        if expected is not None:result['lower_quadrant']=probability(vs,lambda v:v[0]<=.5 and v[1]<=.5,expected)
        if name=='vector_gaussian_copula':
            norm=statistics.NormalDist();z=[[norm.inv_cdf(min(1-1e-9,max(1e-9,x))) for x in v] for v in vs]
            covariance=statistics.fmean(x*y for x,y in z)
            require(abs(covariance-.5)<8*math.sqrt(1.25/len(z))+.01,'Gaussian copula latent covariance')
            result['latent_covariance']=covariance
        return result
    if name=='vector_student_t':
        for j in range(2):cdf_check([v[j] for v in vs],student5_cdf)
        return {'mean_x':mean_check([v[0] for v in vs],0,5/3)}
    if name=='vector_correlated_exponential':
        cdf_check([v[0] for v in vs],lambda x:-math.expm1(-x),lambda x:x>=0)
        return cdf_check([v[1] for v in vs],lambda x:-math.expm1(-2*x),lambda x:x>=0)
    if name=='vector_reward_phase_type':
        require(all(abs(y-2*x)<=1/scale for x,y in vs),'shared reward holding time lost')
        return cdf_check([v[0] for v in vs],lambda x:-math.expm1(-x),lambda x:x>=0)
    raise AssertionError('missing vector oracle '+name)
