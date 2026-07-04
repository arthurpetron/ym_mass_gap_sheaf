"""Exact-rational Wigner 6j / Racah W: signed-square kernel, Biedenharn-Elliott
pentagon, orthogonality, smallest-tetrahedron pin.  Mirrors the Lean
``PentagonNumericCore`` (``PentagonRelation.lean``): the load-bearing datum is
the rational Racah kernel ``P = dim(e) dim(f) {6j}^2`` pinned at the smallest
SU(2) tetrahedron to ``P = 1/4 in {0,1}``.

Conventions (pinned to the Lean kernel)
---------------------------------------
* **Spins internal as** ``fractions.Fraction`` (mirrors
  ``su2_representations.py::Irrep.from_spin``).  A doubled-int adapter ``s = 2j``
  matches ``Rep = Nat = 2j`` / ``dimRep x = x + 1`` (``from_doubled``).
* **mk6 wiring**: ``sixj_symbol(a, b, c, d, e, f) = {a b e; c d f}`` -- top row
  ``a b e``, bottom row ``c d f``; slots 5, 6 are the internal channels
  ``e, f``.  This matches ``PentagonRelation.mk6`` (``smallestTetra =
  mk6 1 1 1 1 2 2`` is doubled-int ``{1/2 1/2 1; 1/2 1/2 1}``).
* **Exact rational only.**  No ``Real`` / ``float`` in the kernel path (Lean
  policy).  Individual SU(2) 6j symbols are generically *irrational* (they are
  ``S * sqrt(prod Delta^2)`` with ``prod Delta^2`` not a perfect square), so the
  kernel carries them as an exact **quadratic radical** ``QuadRadical``
  (``coeff * sqrt(rad)``, ``rad`` a squarefree positive integer over the smooth
  prime base ``{2, 3, 5, 7, ...}`` coming from factorials).  ``{6j}^2`` is always
  an exact ``Fraction``.

Why the identities stay exact-rational
--------------------------------------
In both verified identities the *radicand* of every summed 6j product is
**independent of the summation index** ``x`` and **identical on both sides**:

* Pentagon term ``{a b x; c d p}{c d x; e f q}{e f x; b a r}`` -- the three
  ``x``-carrying triangles ``(a,b,x),(c,d,x),(e,f,x)`` each appear twice and
  square away; the surviving radicand
  ``Delta^2(a,d,p) Delta^2(c,b,p) Delta^2(c,f,q) Delta^2(e,d,q)
  Delta^2(e,a,r) Delta^2(b,f,r)`` matches, triangle-for-triangle, the RHS
  radicand of ``{p q r; e a d}{p q r; f b c}``.
* Orthogonality term ``{a b x; c d p}{a b x; c d q}`` -- ``(a,b,x),(c,d,x)``
  square away, leaving the ``x``-free radicand
  ``Delta^2(a,d,p) Delta^2(c,b,p) Delta^2(a,d,q) Delta^2(c,b,q)``.

So each side is ``(rational cofactor) * sqrt(common radicand)`` and the residual
``LHS - RHS`` is a *single* ``QuadRadical`` whose coefficient is an exact
``Fraction`` -- zero exactly when the identity holds.

Constructive law
----------------
Verification routines return the witnessing object (an exact ``Fraction``
residual or a ``SixJValue``), never a bare boolean (mirrors
``su2_representations.py``).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt
from typing import Optional

Spin = Fraction

# Prime base large enough to fully factor every factorial ratio that occurs for
# spins <= a few (all prime factors of n! for the n we ever hit are <= n).
_PRIMES: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)


# --------------------------------------------------------------------------- #
# Exact quadratic radical:  coeff * sqrt(rad),  rad a squarefree positive int.  #
# --------------------------------------------------------------------------- #
def _squarefree_int(n: int) -> tuple[int, int]:
    """Factor ``n = s^2 * m`` with ``m`` squarefree; return ``(s, m)``.

    ``n`` is a product/ratio numerator of factorials, hence smooth over
    ``_PRIMES``; we factor over that base and split even/odd exponents.  A
    residual ``!= 1`` (a large prime factor) is handled by the ``isqrt``
    fallback so the routine is total.
    """
    if n < 0:
        raise ValueError(f"squarefree extraction needs n >= 0; got {n}")
    if n == 0:
        return 0, 0
    s, m, rem = 1, 1, n
    for p in _PRIMES:
        if p * p > rem:
            break
        e = 0
        while rem % p == 0:
            rem //= p
            e += 1
        s *= p ** (e // 2)
        if e % 2:
            m *= p
    if rem > 1:
        # Fallback for any leftover (should not trigger for our smooth inputs).
        root = isqrt(rem)
        if root * root == rem:
            s *= root
        else:
            m *= rem
    return s, m


@dataclass(frozen=True)
class QuadRadical:
    """Exact ``coeff * sqrt(rad)`` with ``rad`` a squarefree positive integer.

    Canonical zero is ``coeff == 0, rad == 1``.  This is the exact carrier for a
    (generically irrational) SU(2) 6j value; ``{6j}^2 = coeff^2 * rad`` is always
    rational.
    """

    coeff: Fraction
    rad: int

    @classmethod
    def zero(cls) -> "QuadRadical":
        return cls(Fraction(0), 1)

    @classmethod
    def from_coeff_radicand(cls, coeff: Fraction, radicand: Fraction) -> "QuadRadical":
        """Build ``coeff * sqrt(radicand)`` for a nonneg rational ``radicand``."""
        if radicand < 0:
            raise ValueError(f"radicand must be >= 0; got {radicand}")
        if coeff == 0 or radicand == 0:
            return cls.zero()
        # sqrt(p/q) = sqrt(p*q) / q; reduce sqrt(p*q) = s*sqrt(m).
        p, q = radicand.numerator, radicand.denominator
        s, m = _squarefree_int(p * q)
        return cls(coeff * Fraction(s, q), m)

    @property
    def square(self) -> Fraction:
        """The exact rational ``value^2 = coeff^2 * rad``."""
        return self.coeff * self.coeff * self.rad

    def is_zero(self) -> bool:
        return self.coeff == 0

    def __mul__(self, other: object) -> "QuadRadical":
        if isinstance(other, QuadRadical):
            s, m = _squarefree_int(self.rad * other.rad)
            return QuadRadical.from_parts(self.coeff * other.coeff * s, m)
        if isinstance(other, (int, Fraction)):
            return QuadRadical.from_parts(self.coeff * other, self.rad)
        return NotImplemented

    __rmul__ = __mul__

    @classmethod
    def from_parts(cls, coeff: Fraction, rad: int) -> "QuadRadical":
        """Internal constructor that normalizes zero and an already-squarefree
        (or to-be-reduced) ``rad``."""
        if coeff == 0:
            return cls.zero()
        s, m = _squarefree_int(rad)
        return cls(coeff * s, m)

    def __add__(self, other: "QuadRadical") -> "QuadRadical":
        if not isinstance(other, QuadRadical):
            return NotImplemented
        if self.is_zero():
            return other
        if other.is_zero():
            return self
        if self.rad != other.rad:
            raise ValueError(
                "cannot add radicals with distinct radicands "
                f"{self.rad} != {other.rad} (not a single quadratic radical)"
            )
        c = self.coeff + other.coeff
        return QuadRadical.zero() if c == 0 else QuadRadical(c, self.rad)

    def __neg__(self) -> "QuadRadical":
        return QuadRadical.zero() if self.is_zero() else QuadRadical(-self.coeff, self.rad)

    def __sub__(self, other: "QuadRadical") -> "QuadRadical":
        return self + (-other)

    def to_fraction(self) -> Fraction:
        """Exact ``Fraction`` value; requires the radical to be rational.

        Rational exactly when ``coeff == 0`` (value 0) or ``rad == 1``.  The
        verified residuals are always 0, so this never raises on the checks.
        """
        if self.coeff == 0:
            return Fraction(0)
        if self.rad == 1:
            return self.coeff
        raise ValueError(f"radical {self.coeff}*sqrt({self.rad}) is irrational")

    def value_or_none(self) -> Optional[Fraction]:
        """Signed value as a ``Fraction`` when rational, else ``None``."""
        if self.coeff == 0:
            return Fraction(0)
        return self.coeff if self.rad == 1 else None


# --------------------------------------------------------------------------- #
# SixJValue: the returned object (square + sign, per the constructive law).     #
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class SixJValue:
    """A Wigner 6j value as ``(square, sign)``: ``{6j}^2`` (exact rational) and
    ``sgn({6j}) in {-1, 0, +1}``.  ``value_or_none`` recovers the signed ``|6j|``
    only when ``square`` is a perfect rational square."""

    square: Fraction
    sign: int

    @classmethod
    def from_radical(cls, qr: QuadRadical) -> "SixJValue":
        if qr.coeff == 0:
            return cls(Fraction(0), 0)
        return cls(qr.square, 1 if qr.coeff > 0 else -1)

    def value_or_none(self) -> Optional[Fraction]:
        if self.square == 0:
            return Fraction(0)
        p, q = self.square.numerator, self.square.denominator
        rp, rq = isqrt(p), isqrt(q)
        if rp * rp == p and rq * rq == q:
            return self.sign * Fraction(rp, rq)
        return None


# --------------------------------------------------------------------------- #
# Exact factorial / triangle / delta helpers.                                  #
# --------------------------------------------------------------------------- #
def _fact(n: int) -> int:
    if n < 0:
        raise ValueError(f"factorial argument must be >= 0; got {n}")
    return factorial(n)


def _is_halfint(x: Spin) -> bool:
    return (2 * x).denominator == 1


def triangle_ok(a: Spin, b: Spin, c: Spin) -> bool:
    """Triangle condition: half-integer spins, ``a + b + c in Z`` and
    ``|a - b| <= c <= a + b``."""
    if not (_is_halfint(a) and _is_halfint(b) and _is_halfint(c)):
        return False
    if a < 0 or b < 0 or c < 0:
        return False
    if (a + b + c).denominator != 1:
        return False
    return abs(a - b) <= c <= a + b


def delta_squared(a: Spin, b: Spin, c: Spin) -> Fraction:
    """``Delta(a,b,c)^2 = (a+b-c)!(a-b+c)!(-a+b+c)! / (a+b+c+1)!`` (0 if no
    triangle)."""
    if not triangle_ok(a, b, c):
        return Fraction(0)
    num = _fact(int(a + b - c)) * _fact(int(a - b + c)) * _fact(int(-a + b + c))
    den = _fact(int(a + b + c + 1))
    return Fraction(num, den)


# --------------------------------------------------------------------------- #
# Core Racah single sum + 6j square/value.                                      #
# --------------------------------------------------------------------------- #
def racah_sum(
    j1: Spin, j2: Spin, j3: Spin, j4: Spin, j5: Spin, j6: Spin
) -> Fraction:
    """The exact Racah single sum ``S`` of ``{j1 j2 j3; j4 j5 j6}``.

    ``S = sum_t (-1)^t (t+1)! / [ prod_triads (t - T)! * prod_quads (Q - t)! ]``,
    ``t`` from ``max(triads)`` to ``min(quads)``.  Returns 0 outside that range.
    """
    triads = [j1 + j2 + j3, j1 + j5 + j6, j4 + j2 + j6, j4 + j5 + j3]
    quads = [j1 + j2 + j4 + j5, j2 + j3 + j5 + j6, j1 + j3 + j4 + j6]
    t_lo, t_hi = max(triads), min(quads)
    if t_lo > t_hi:
        return Fraction(0)
    if (t_lo).denominator != 1 or (t_hi).denominator != 1:
        return Fraction(0)
    total = Fraction(0)
    for t in range(int(t_lo), int(t_hi) + 1):
        den = 1
        for tri in triads:
            den *= _fact(t - int(tri))
        for qu in quads:
            den *= _fact(int(qu) - t)
        term = Fraction((-1) ** t * _fact(t + 1), den)
        total += term
    return total


def _sixj_radical(
    j1: Spin, j2: Spin, j3: Spin, j4: Spin, j5: Spin, j6: Spin
) -> QuadRadical:
    """``{j1 j2 j3; j4 j5 j6}`` as an exact quadratic radical
    ``S * sqrt(prod Delta^2)``; zero if any of the four triangles fail."""
    tris = [(j1, j2, j3), (j1, j5, j6), (j4, j2, j6), (j4, j5, j3)]
    if not all(triangle_ok(*t) for t in tris):
        return QuadRadical.zero()
    prod_delta2 = Fraction(1)
    for t in tris:
        prod_delta2 *= delta_squared(*t)
    s = racah_sum(j1, j2, j3, j4, j5, j6)
    if s == 0:
        return QuadRadical.zero()
    return QuadRadical.from_coeff_radicand(s, prod_delta2)


def sixj_squared(
    j1: Spin, j2: Spin, j3: Spin, j4: Spin, j5: Spin, j6: Spin
) -> SixJValue:
    """``SixJValue`` of the standard symbol ``{j1 j2 j3; j4 j5 j6}``."""
    return SixJValue.from_radical(_sixj_radical(j1, j2, j3, j4, j5, j6))


def sixj_symbol(
    a: Spin, b: Spin, c: Spin, d: Spin, e: Spin, f: Spin
) -> SixJValue:
    """mk6 adapter: ``SixJValue`` of ``{a b e; c d f}``."""
    return SixJValue.from_radical(_sixj_radical(a, b, e, c, d, f))


def _sixj_symbol_radical(
    a: Spin, b: Spin, c: Spin, d: Spin, e: Spin, f: Spin
) -> QuadRadical:
    """mk6 wiring returning the exact radical of ``{a b e; c d f}``."""
    return _sixj_radical(a, b, e, c, d, f)


def dim(j: Spin) -> Fraction:
    """Dimension of the spin-``j`` irrep, ``2j + 1`` (``dimRep`` in doubled
    ints)."""
    return 2 * j + 1


def racah_kernel(
    a: Spin, b: Spin, c: Spin, d: Spin, e: Spin, f: Spin
) -> Fraction:
    """The Lean ``PentagonNumericCore`` object
    ``P = dim(e) dim(f) {a b e; c d f}^2`` (exact rational)."""
    return dim(e) * dim(f) * sixj_symbol(a, b, c, d, e, f).square


# --------------------------------------------------------------------------- #
# Verification targets (witness = exact Fraction residual).                     #
# --------------------------------------------------------------------------- #
def biedenharn_elliott_residual(
    a: Spin, b: Spin, c: Spin, d: Spin, e: Spin, f: Spin,
    p: Spin, q: Spin, r: Spin,
) -> Fraction:
    """Exact ``|LHS - RHS|`` of the Biedenharn-Elliott pentagon (all-Delta
    guarded form).

    ``sum_x (-1)^{a+b+c+d+e+f+p+q+r+x} (2x+1)
        {a b x; c d p}{c d x; e f q}{e f x; b a r}
      = {p q r; e a d}{p q r; f b c}``

    Both sides share one common radicand, so the residual is an exact
    ``Fraction`` (zero when the identity holds).
    """
    x_lo = max(abs(a - b), abs(c - d), abs(e - f))
    x_hi = min(a + b, c + d, e + f)
    lhs = QuadRadical.zero()
    two_x = int(2 * x_lo)
    while two_x <= int(2 * x_hi):
        x = Fraction(two_x, 2)
        w1 = _sixj_symbol_radical(a, b, c, d, x, p)
        w2 = _sixj_symbol_radical(c, d, e, f, x, q)
        w3 = _sixj_symbol_radical(e, f, b, a, x, r)
        two_x += 2
        if w1.is_zero() or w2.is_zero() or w3.is_zero():
            continue
        exponent = a + b + c + d + e + f + p + q + r + x
        if exponent.denominator != 1:
            # A nonzero term with half-integer phase would make the identity
            # non-real; the triangle constraints preclude this.
            raise ValueError(f"non-integer phase exponent {exponent}")
        sign = (-1) ** int(exponent)
        lhs = lhs + (sign * (2 * x + 1)) * (w1 * w2 * w3)
    rhs_l = _sixj_symbol_radical(p, q, e, a, r, d)  # {p q r; e a d}
    rhs_r = _sixj_symbol_radical(p, q, f, b, r, c)  # {p q r; f b c}
    residual = lhs - (rhs_l * rhs_r)
    return abs(residual.to_fraction())


def _spins(j_max: Spin) -> list[Spin]:
    n = int(2 * j_max)
    return [Fraction(k, 2) for k in range(n + 1)]


def pentagon_sweep(j_max: Spin = Fraction(2)) -> tuple[Fraction, tuple]:
    """Max exact ``|LHS - RHS|`` of the pentagon over the non-vacuous sweep
    (spins in ``{0, 1/2, ..., j_max}`` with all RHS triangles satisfied) plus
    the arg-max tuple.

    Vacuous configurations (a broken RHS triangle) have ``RHS = 0`` and, by the
    Biedenharn-Elliott identity, ``LHS = 0``; they are pruned for speed, leaving
    only genuinely non-vacuous checks (both sides nonzero).
    """
    spins = _spins(j_max)
    worst = Fraction(0)
    arg: tuple = ()
    # RHS triangles that must hold for a non-vacuous check:
    #   {p q r; e a d}: (p,q,r),(p,a,d),(e,q,d),(e,a,r)
    #   {p q r; f b c}: (p,q,r),(p,b,c),(f,q,c),(f,b,r)
    for p in spins:
        for q in spins:
            for r in spins:
                if not triangle_ok(p, q, r):
                    continue
                for a in spins:
                    for d in spins:
                        if not triangle_ok(p, a, d):
                            continue
                        for e in spins:
                            if not (triangle_ok(e, a, r) and triangle_ok(e, q, d)):
                                continue
                            for b in spins:
                                for c in spins:
                                    if not triangle_ok(p, b, c):
                                        continue
                                    for f in spins:
                                        if not (
                                            triangle_ok(f, q, c)
                                            and triangle_ok(f, b, r)
                                        ):
                                            continue
                                        res = biedenharn_elliott_residual(
                                            a, b, c, d, e, f, p, q, r
                                        )
                                        if res > worst:
                                            worst = res
                                            arg = (a, b, c, d, e, f, p, q, r)
    return worst, arg


def orthogonality_residual(
    a: Spin, b: Spin, c: Spin, d: Spin, p: Spin, q: Spin
) -> Fraction:
    """Exact ``|sum_x (2x+1){a b x; c d p}{a b x; c d q} - delta_{pq}/(2p+1)|``.

    The two ``x``-carrying triangles square away leaving one common ``x``-free
    radicand, so the residual is an exact ``Fraction`` (0 when the identity
    holds; ``p, q`` restricted to valid channels)."""
    x_lo = max(abs(a - b), abs(c - d))
    x_hi = min(a + b, c + d)
    lhs = QuadRadical.zero()
    two_x = int(2 * x_lo)
    while two_x <= int(2 * x_hi):
        x = Fraction(two_x, 2)
        wp = _sixj_symbol_radical(a, b, c, d, x, p)
        wq = _sixj_symbol_radical(a, b, c, d, x, q)
        two_x += 2
        if wp.is_zero() or wq.is_zero():
            continue
        lhs = lhs + (2 * x + 1) * (wp * wq)
    rhs = Fraction(1, int(2 * p + 1)) if p == q else Fraction(0)
    return abs(lhs.to_fraction() - rhs)


def _valid_channels(a: Spin, b: Spin, c: Spin, d: Spin, spins: list[Spin]) -> list[Spin]:
    """Channels ``p`` with ``{a b x; c d p}`` possibly nonzero: triangles
    ``(a,d,p)`` and ``(c,b,p)``."""
    return [p for p in spins if triangle_ok(a, d, p) and triangle_ok(c, b, p)]


def orthogonality_sweep(j_max: Spin = Fraction(2)) -> tuple[Fraction, tuple]:
    """Max exact orthogonality residual over spins in ``{0, ..., j_max}`` (with
    ``p, q`` ranging over valid channels), plus the arg-max tuple."""
    spins = _spins(j_max)
    worst = Fraction(0)
    arg: tuple = ()
    for a in spins:
        for b in spins:
            for c in spins:
                for d in spins:
                    channels = _valid_channels(a, b, c, d, spins)
                    for p in channels:
                        for q in channels:
                            res = orthogonality_residual(a, b, c, d, p, q)
                            if res > worst:
                                worst = res
                                arg = (a, b, c, d, p, q)
    return worst, arg


def smallest_tetra_pin() -> SixJValue:
    """The load-bearing pin ``{1/2 1/2 1; 1/2 1/2 1}``.

    The 6j value is ``1/6`` (``square = 1/36``, ``sign = +1``); the Lean object
    is the Racah *kernel* ``P = dim(1) dim(1) (1/6)^2 = 3*3/36 = 1/4`` (see
    ``smallest_tetra_kernel``), matching ``PentagonNumericCore.smallest_value``
    / ``oneQuarter = 1/4 in {0,1}``."""
    return sixj_symbol(
        Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2),
        Fraction(1), Fraction(1),
    )


def smallest_tetra_kernel() -> Fraction:
    """The Lean ``oneQuarter`` object: ``P = dim(e)dim(f){6j}^2 = 1/4`` at the
    smallest SU(2) tetrahedron ``{1/2 1/2 1; 1/2 1/2 1}``."""
    return racah_kernel(
        Fraction(1, 2), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2),
        Fraction(1), Fraction(1),
    )


# --------------------------------------------------------------------------- #
# Doubled-int adapter (mk6 tuples).                                             #
# --------------------------------------------------------------------------- #
def from_doubled(s_tuple: tuple[int, ...]) -> tuple[Spin, ...]:
    """Convert doubled-int labels ``s = 2j`` to spins ``j`` (``Rep = 2j``)."""
    return tuple(Fraction(s, 2) for s in s_tuple)


# --------------------------------------------------------------------------- #
# CLI results table.                                                           #
# --------------------------------------------------------------------------- #
def _fmt_spin(j: Spin) -> str:
    return str(j.numerator) if j.denominator == 1 else f"{j.numerator}/{j.denominator}"


def _fmt_value(v: SixJValue) -> str:
    exact = v.value_or_none()
    if exact is not None:
        return f"{exact}"
    return f"sign {v.sign:+d} * sqrt({v.square})  (irrational)"


def _print_summary() -> None:
    print("SU(2) Wigner 6j / Racah kernel (exact rational; mk6 = {a b e; c d f})\n")
    spins = [Fraction(1, 2), Fraction(1)]
    print("  small-spin table  {a b e; c d f} -> ({6j}, {6j}^2, P=dim(e)dim(f){6j}^2)")
    for a in spins:
        for e in spins:
            v = sixj_symbol(a, a, a, a, e, e)
            if v.sign == 0:
                continue
            P = racah_kernel(a, a, a, a, e, e)
            label = (
                f"{{{_fmt_spin(a)} {_fmt_spin(a)} {_fmt_spin(e)}; "
                f"{_fmt_spin(a)} {_fmt_spin(a)} {_fmt_spin(e)}}}"
            )
            print(f"    {label:<28} 6j = {_fmt_value(v):<10}  6j^2 = {v.square}  P = {P}")

    print("\n  witness rows")
    pin = smallest_tetra_pin()
    print(
        f"    smallest tetra {{1/2 1/2 1; 1/2 1/2 1}}: 6j = {_fmt_value(pin)}, "
        f"6j^2 = {pin.square}, sign = {pin.sign:+d}"
    )
    print(
        f"    Racah kernel  P = {smallest_tetra_kernel()}  "
        f"(Lean oneQuarter = 1/4, in {{0,1}} refuted)"
    )
    pmax, parg = pentagon_sweep()
    print(f"    Biedenharn-Elliott pentagon: max residual = {pmax}  (arg {parg})")
    omax, oarg = orthogonality_sweep()
    print(f"    orthogonality:               max residual = {omax}  (arg {oarg})")


if __name__ == "__main__":
    _print_summary()
