"""Exact finite upper-bound certificate for the low-probability wrapper defect.

This is rational arithmetic on the reviewed finite-walk laws, not an interpreter
test. Unknown recursive calls at depth six optimistically return true. Each
finite inner loop has a polynomial with nonnegative coefficients, so replacing
its recursive success probability by an upper bound preserves an upper bound.
"""

from fractions import Fraction as Q


def walk_transform(child: Q, next_bias: Q, height: int) -> Q:
    """The outer gambler and its finite high-power retry loop."""
    inner = Q(0)
    for h in range(2, height + 1):
        exponent = h - 2
        stop = next_bias ** exponent / sum(
            (next_bias ** j for j in range(exponent + 1)), Q(0))
        inner = child * (stop + (1 - stop) * inner)
    gambler = next_bias * sum((next_bias ** j for j in range(height - 1)), Q(0))
    gambler /= sum((next_bias ** j for j in range(height)), Q(0))
    return gambler * (Q(height - 1, height) + inner / height)


def certificate() -> tuple[Q, Q]:
    # LLP(a=2,b=1,m=1,n=4,p=1/8) calls Linear(8,2,3,4).
    p = Q(1, 8)
    a, b, e, f = 8, 2, 3, 4
    states = []
    while Q(a, b) * p <= 1:
        height = (9 * f + 2 * e - 1) // (2 * e) + 1
        states.append((a, b, height))
        a, b, e, f = a * height, b * (height - 1), height * e - f, (height - 1) * f
    assert len(states) == 6 and Q(a, b) * p == Q(15, 14)
    upper = Q(1)
    scale = 2 ** 64
    for a, b, height in reversed(states):
        next_bias = Q(a * height, b * (height - 1)) * p
        # Algebraically, the intended (possibly >1) child bias would give a*p/b.
        assert walk_transform(next_bias, next_bias, height) == Q(a, b) * p
        bound = walk_transform(upper, next_bias, height)
        numerator = -((-bound.numerator * scale) // bound.denominator)
        upper = Q(numerator, scale)
        assert upper >= bound
    assert upper < Q(1, 2)
    wrapper = Q(1, 3) * (Q(1, 2) + upper / 2)
    assert wrapper == Q(3458761390365312857, 13835058055282163712)
    assert wrapper < Q(1, 4)
    return upper, wrapper


if __name__ == "__main__":
    linear, wrapper = certificate()
    print(f"Linear success probability <= {linear} < 1/2")
    print(f"Wrapper success probability <= {wrapper} < advertised 1/4")
