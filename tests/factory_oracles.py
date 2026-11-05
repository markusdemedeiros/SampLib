"""Independent probability checks for exact and finite-grid factory fixtures.

No random values are generated here. The inputs are actual ProbLang results.
Numerical constant fixtures retain their finite-grid qualification. Critical-walk
minimum factories should use only one smoke draw; they have infinite expected cost.
"""
import math


# Recommended per-case caps for intrinsically heavy exact constructions.
COUNTS = {
    **{f'factory_piecewise{i}': 1 for i in range(6)},
    'factory_minimum': 1, 'factory_minimum_half': 1,
    'constant_euler': 100, 'constant_zeta3': 100,
    'factory_linear': 250, 'factory_linear_power': 250,
    'factory_addition': 250, 'factory_subtraction': 250,
    'factory_division': 250, 'factory_epsilon_division': 250,
    'factory_affine_ratio': 250,
    'factory_exp_nested': 250, 'factory_p_over_tangent': 100,
}


def _lower_gamma_ratio(a, x):
    # Power-series integration of t^(a-1) exp(-t), common Gamma(a) cancels.
    def unnormalized(z):
        term = total = 1.0 / a
        for n in range(1, 200):
            term *= -z / n
            value = term * a / (a+n)
            # term's a denominator remains fixed, so value = (-z)^n/(n!(a+n)).
            total += value
            if abs(value) < 1e-17:
                break
        return z**a * total
    return unnormalized(x)/unnormalized(1.0)


def probability(name, scale):
    p, r, h = .3, .2, .6
    e, pi = math.e, math.pi
    formula = {
        'factory_power': p**(7/3), 'factory_two_power': p**r,
        'factory_two_coin': .75*2*p/(.75*(2*p+3*r)+.25*5),
        'factory_linear': 2*p, 'factory_linear_power': (2*p)**2,
        'factory_addition': p+r, 'factory_subtraction': h-r,
        'factory_division': r/h, 'factory_epsilon_division': .2/h,
        'factory_reciprocal_affine': 1/(2+p), 'factory_affine': (.5+p)/2,
        'factory_affine_ratio': (.2+r)/(1+h),
        'factory_reciprocal_logistic': 1/(1+1.5*p), 'factory_two_minus': 1/(2-p),
        'factory_exp_scaled': math.exp(-2.5*p), 'factory_exp_shifted': math.exp(-.5-p),
        'factory_exp_complement': math.exp(p)*(1-p),
        'factory_alternating': math.log1p(p)/p,
        'factory_positive_series': (1+2*p+3*p*p)/6,
        'factory_complement_series': 1-(1*(1-p)+2*(1-p)**2+3*(1-p)**3)/6,
        'factory_hazards': 1-(1-p)/(1+p),
        'factory_convex': (p+2*r)/3, 'factory_integral': 1/3,
        'factory_envelope': p*p,
        'factory_approximate_square': p*p+p*(1-p)/20,
        'factory_minimum': min(p,1-p), 'factory_minimum_half': min(p,.5),
        'factory_complement_ratio': (1-p)/(1+p),
        'factory_sigmoid': 1/(1+math.exp(2/3)),
        'factory_sigmoid_scaled': 1/(1+math.exp(-1.5*p)),
        'factory_logistic_exp': 1/(1+math.exp(.75)),
        'factory_tanh': math.tanh(2/3), 'factory_tanh_scaled': math.tanh(1.5*p),
        'factory_tanh_shifted': math.tanh((.5+p)/2),
        'factory_twist': p*math.exp(2/3)/(p*math.exp(2/3)+1-p),
        'factory_exp_ratio': (1+math.exp(2/3-.5))/(1+math.exp(2/3)),
        'factory_inverse_quadratic': 1/(1+(1+p)**2),
        'factory_reciprocal_power': (1/(2+p))**2,
        'factory_offset_race': (.5+r)/(1+p+.5+r),
        'factory_exp_integral0': -math.expm1(-p)/p,
        'factory_exp_integral1': -math.expm1(-1-p)/(1+p),
        'factory_log_affine': math.log(2+p)/(2+p),
        'factory_sinc': math.sin(p*math.sqrt(2))/(p*math.sqrt(2)),
        'factory_cos_sqrt': math.cos(math.sqrt(p)),
        'factory_exp_polynomial': math.exp(-.2-.5*p-p*p/3),
        'factory_exp_shift_power': math.exp(-(1+p)**2),
        'factory_exp_div_three': math.exp(p)/3,
        'factory_exp_nested': math.exp(-math.exp(p)),
        'factory_polynomial': .2+.5*p-.2*p*p,
        'factory_rational_function': (.2+.5*p)/(.6+.3*p),
        'factory_piecewise0': .18, 'factory_piecewise1': .46,
        'factory_piecewise2': .06, 'factory_piecewise3': .38,
        'factory_piecewise4': .7, 'factory_piecewise5': .38,
        'factory_arctan_pi': math.atan(p)/pi,
        'factory_sinc_sqrt': math.sin(math.sqrt(2*p))/math.sqrt(2*p),
        'factory_p_log_inverse': -p*math.log(p),
        'factory_complement_log_inverse': -(1-p)*math.log1p(-p),
        'factory_p_over_log_inverse': p/(-math.log1p(-p)),
        'factory_complement_over_log_inverse': (1-p)/(-math.log(p)),
        'factory_polylogarithm': sum(p**k/(k*k) for k in range(1,200))*(1/p-1),
        'factory_complement_cos': (1-p)/math.cos(p),
        'factory_complement_tan': (1-p)*math.tan(p),
        'factory_arcsine_sqrt': math.asin(p)+math.sqrt(1-p*p)-1,
        'factory_arcsine_half': math.asin(p)/2,
        'factory_exp_square_complement': math.exp(p*p)*(1-p),
        'factory_reciprocal_exp_affine': 1/(2+math.exp(-.5)),
        'factory_one_plus_half': (1+p)/2, 'factory_complement_half': (1-p)/2,
        'factory_complement_log_one_plus': 1-math.log1p(p),
        'factory_odds_product': r*p/(1-r+r*p),
        'factory_sigmoid_derivative': math.exp(2/3)/(1+math.exp(2/3))**2,
        'factory_binary_exp': 2**(-2*(1+p)),
        'factory_binary_exp_rational': 2**(-1.5*p),
        'factory_p_over_tangent': h/math.tan(h), 'factory_envelope_degrees': p*p,
        'constant_digits': 1/3, 'constant_approx_digits': 1/3,
        'constant_bounds': .4, 'constant_positive_series': 1/3,
        'constant_continued_fraction': 3/5,
        'constant_generalized_fraction': 3/8, 'constant_continued_log': 2/3,
        'constant_golden': (math.sqrt(5)-1)/2,
        'constant_sqrt2minus1': math.sqrt(2)-1, 'constant_inverse_sqrt2': 1/math.sqrt(2),
        'constant_pi_quarter': pi/4, 'constant_pi_twelfth': pi/12,
        'constant_pi_quarter_minus_half': pi/4-.5,
        'constant_pi_minus3_over4': (pi-3)/4, 'constant_pi_minus3': pi-3,
        'constant_inverse_pi': 1/pi, 'constant_four_over_three_pi': 4/(3*pi),
        'constant_e_minus2': e-2, 'constant_e_third': e/3, 'constant_e_quarter': e/4,
        'constant_three_minus_e': 3-e, 'constant_inverse_e_plus': 1/e,
        'constant_tanh_half': math.tanh(.5),
        'constant_zeta3': .9015426773696957, 'constant_zeta_related': .9015426773696957,
        'constant_euler': .5772156649015329,
        'constant_log_rational': math.log(1+2/3), 'constant_logpi_overpi': math.log(pi)/pi,
        'constant_integer_power': (2/3)**4,
        'constant_exp_product': math.exp(-2/3)*1.5,
        'constant_golden_family': ((math.sqrt(5)-1)/2)**2,
        'constant_e_overpi': e/pi, 'constant_inverse_sqrtpi': 1/math.sqrt(pi),
        'constant_arctan_ratio': math.atan(2/3)/(2/3),
        'constant_erf_ratio': math.erf(.5)/math.erf(1),
        'constant_gamma_integer': _lower_gamma_ratio(2,.5),
        'constant_numerical_power': (2/3)**1.5,
        'constant_numerical_gamma': _lower_gamma_ratio(1.5,.5),
        'constant_numerical_euler': .5772156649015329,
        'constant_numerical_exp_product': math.exp(-2/3)*1.5,
        'constant_numerical_logpi': math.log(pi)/pi,
    }
    return formula.get(name)


def check(name, raw_values, scale):
    p = probability(name, scale)
    if p is None:
        return None
    if not raw_values or any(type(v) is not bool for v in raw_values):
        raise AssertionError(f'{name}: expected nonempty Boolean outputs')
    n, observed = len(raw_values), sum(raw_values)
    log = math.log(2/1e-9)
    tolerance = math.sqrt(2*n*p*(1-p)*log)+2*log/3
    # Grid approximations have small additional allowance, not an exactness claim.
    if 'numerical' in name or name == 'factory_approximate_square':
        tolerance += n*.003
    if abs(observed-n*p) > tolerance:
        raise AssertionError(f'{name}: {observed}/{n}, expected p={p:.12g}, count bound={tolerance:.5g}')
    return {'expected_probability': p, 'observed_probability': observed/n,
            'frequency_bound': tolerance/n, 'numerical': 'numerical' in name,
            'smoke_only': n <= 1}
