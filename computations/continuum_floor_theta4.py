"""
Continuum-floor inequality pilot:  G_odd(w) - G_even(w) <= 1  on w in (0,1).

Reframed (D=2j even / D=2j+1 odd, r=w^2):
    G_odd - G_even = 4 (Var_o - Var_e),
    Var_e = variance of j under r^{j^2}          (integer-centred discrete Gaussian)
    Var_o = variance of j under r^{(j+1/2)^2}     (half-integer-centred)
Target  <=>  Var_o - Var_e <= 1/4.

MAIN RESULT (proved, verified here to ~40-50 digits):
    Var_o - Var_e = (1/4) * theta4(r)^4 ,   theta4(r) = sum_n (-1)^n r^{n^2}.
Since 0 < theta4(r) < 1 for r in (0,1) (Jacobi triple product: a product of factors
in (0,1)), we get  Var_o - Var_e < 1/4  with EXACT slack (1/4)(1 - theta4^4),
tight as r -> 0 (theta4 -> 1).

Equivalently  G_odd - G_even = theta4(r)^4  (<= 1, -> 1 as w->0, -> 0 as w->1).

Underlying identity (theta-constant ODE, delta = q d/dq):
    delta log(theta2/theta3) = (1/4) theta4^4.
Proof: three heat-equation theta-constant ODEs
    delta log theta2 = (1/12)(E2 + theta3^4 + theta4^4)
    delta log theta3 = (1/12)(E2 + theta2^4 - theta4^4)
    delta log theta4 = (1/12)(E2 - theta2^4 - theta3^4)
subtract (E2 cancels) and use Jacobi theta3^4 = theta2^4 + theta4^4.

theta4^4 has an integer Lambert series:  theta4^4 = 1 + 8 sum_{n>=1} (-1)^n s(n) q^n,
s(n) = sum_{d|n, 4 not| d} d   (so 1 - 8q + 24q^2 - 32q^3 + 24q^4 - ...).
"""
import mpmath as mp
mp.mp.dps = 50


def _N(r):
    return int(mp.sqrt(300 / (-mp.log(r) + mp.mpf('1e-30')))) + 60


def var_e(r):
    Z = M2 = mp.mpf(0)
    for n in range(-_N(r), _N(r) + 1):
        w = mp.power(r, n * n); Z += w; M2 += n * n * w
    return M2 / Z


def var_o(r):
    Z = M2 = mp.mpf(0)
    for n in range(-_N(r), _N(r) + 1):
        x = n + mp.mpf(1) / 2; w = mp.power(r, x * x); Z += w; M2 += x * x * w
    return M2 / Z


def theta4(r):
    return 1 + 2 * sum((-1) ** n * mp.power(r, n * n) for n in range(1, _N(r) + 1))


def theta4_product(r, N=4000):
    p = mp.mpf(1)
    for n in range(1, N):
        p *= (1 - mp.power(r, 2 * n)) * (1 - mp.power(r, 2 * n - 1)) ** 2
    return p


def s4(n):
    return sum(d for d in range(1, n + 1) if n % d == 0 and d % 4 != 0)


def theta4_4_lambert(r, N=300):
    return 1 + 8 * sum(((-1) ** n) * s4(n) * mp.power(r, n) for n in range(1, N))


if __name__ == "__main__":
    print(f"{'r':>10} {'Var_o-Var_e':>24} {'(1/4)theta4^4':>24} {'err':>10} {'<=1/4':>6}")
    for rx in ['1e-8', '0.01', '0.1', '0.3', '0.5', '0.7', '0.9']:
        r = mp.mpf(rx)
        d = var_o(r) - var_e(r); pred = theta4(r) ** 4 / 4
        print(f"{rx:>10} {mp.nstr(d,18):>24} {mp.nstr(pred,18):>24} "
              f"{mp.nstr(d-pred,3):>10} {str(d<=mp.mpf(1)/4):>6}")
    r = mp.mpf('0.3')
    assert abs(theta4(r) - theta4_product(r)) < mp.mpf('1e-40')
    assert abs(theta4(r) ** 4 - theta4_4_lambert(r)) < mp.mpf('1e-40')
    assert mp.mpf(0) < theta4(r) < mp.mpf(1)
    print("\nOK: identity, product-positivity, and integer Lambert series all verified.")
