"""Exact rational diagnostic, NOT a Yang--Mills computation or Lean certificate.

A strictly gapped positive diagonal transfer on a vacuum complement can
retain a macroscopic response while failing the sufficient factor-two window
cost test. The finite examples below check the hand calculation in the
adaptive-score audit. They prove no statement about the original YM carrier,
changing-family survival, or a continuum Hamiltonian.
"""

from fractions import Fraction


def check_example(u: int) -> None:
    assert u >= 1
    lam = Fraction(1, 100)
    mu = 1 - Fraction(1, 4 * u)

    # T = diag(1, mu, lam), vacuum = e0, x = (0, lam**u, mu**u).
    def response(n: int) -> Fraction:
        return lam ** (2 * u) * mu**n + mu ** (2 * u) * lam**n

    cost = sum(
        (response(2 * t) - response(2 * t + 1) for t in range(u, 2 * u)),
        Fraction(0),
    )
    assert 0 < lam < mu < 1
    assert response(0) <= 2
    assert response(2 * u) == 2 * (lam * mu) ** (2 * u) > 0
    assert mu ** (2 * u) >= Fraction(1, 2)
    assert response(4 * u) / response(2 * u) >= Fraction(1, 4)
    assert 2 * cost / response(2 * u) == (
        (1 - mu ** (2 * u)) / (1 + mu)
        + (1 - lam ** (2 * u)) / (1 + lam)
    )
    assert 1 - 2 * cost / response(2 * u) <= -Fraction(23, 200)
    assert response(2 * u) / response(0) <= 2 * lam ** (2 * u)


if __name__ == "__main__":
    for window in (1, 8, 64):
        check_example(window)
    print("PASS: three exact two-mode diagnostics; no YM or Lean proof input.")
