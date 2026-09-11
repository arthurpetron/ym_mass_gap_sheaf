"""MD.2 (SU(2) half, step 0) — the exact flat representation of the
SU(2) heat kernel, in repo conventions.

**Why.**  The U(1) lane was solved by Poisson-resumming the abelian
theta series (§16b/§16c).  The SU(2) analogue of that step is the
classical exact image-sum ("strict flatness") representation of the
SU(2) heat kernel: in the repo's conventions — activity variable
s = e^{-tau}, character expansion

    K(phi; s) = sum_{n >= 0} d_n s^{C(n)} chi_n,
    d_n = n + 1,  C(n) = n(n+2) = (n+1)^2 - 1,
    chi_n = sin((n+1) phi) / sin(phi),      phi in (0, pi)

(phi the HALF-angle of the class: g ~ diag(e^{i phi}, e^{-i phi})) —
the kernel equals EXACTLY a Gaussian image sum on the flat line:

    K(phi; s) = e^{tau} * (sqrt(pi) / (4 tau^{3/2})) * (1 / sin phi)
                * sum_{j in Z} (phi - 2 pi j)
                  * e^{-(phi - 2 pi j)^2 / (4 tau)}.

Derivation (every step classical): the character sum is
(e^{tau}/sin phi) sum_{k >= 1} k e^{-tau k^2} sin(k phi) with
k = n + 1; the summand is even in k, so it equals (1/2) the sum over
k in Z; then sum_k k e^{-tau k^2} sin(k phi)
= -d/dphi sum_k e^{-tau k^2} cos(k phi)
= -d/dphi [ sqrt(pi/tau) sum_j e^{-(phi - 2 pi j)^2/(4 tau)} ]
= sqrt(pi/tau) sum_j ((phi - 2 pi j)/(2 tau))
  e^{-(phi - 2 pi j)^2/(4 tau)}
by the Jacobi theta transform.  The module verifies the identity to
40 digits across a (tau, phi) grid rather than trusting the constant
bookkeeping.

**What it is for.**  Each slab face activity K(U_f; s) becomes, near
s -> 1, a flat Gaussian in the plaquette class angle times explicit
Jacobian factors (phi/sin phi and the e^{tau} normalization) plus
exponentially small images — so the SU(2) slab kernel becomes a flat
Gaussian NETWORK integral with computable correction insertions.
The three places non-abelian dynamics enters, each now an explicit
finite object:
  (i)   the e^{tau} prefactor per face (pure normalization; cancels
        in flow ratios up to face counts),
  (ii)  the measure/Jacobian factors (phi/sin phi per activity,
        sin^2 phi in the Weyl/Haar density),
  (iii) BCH non-closure of the plaquette angle as a function of link
        variables (the first genuinely group-structural term).
The c_SU2 program (§16c route b) is: expand (i)-(iii) to O(tau)
around the Gaussian network whose leading behaviour is group-blind
(E* = 3), with the U(1) mirror of the same expansion required to
reproduce c1 = -4 at N = 2.

**Status.**  This module BANKS the identity as a verified numerical
gate (40+ digits, multiple (s, phi), plus the Haar-normalization and
character-orthogonality gates in the same conventions).  It is
scaffolding for the derivation, not yet a certified-rational object;
certification (rational pi windows + tail bounds, as in
`u1_theta_kernel.slack_bound`) is scoped for the step that first
consumes the identity in a verdict.

Run:  python -m computations.su2_flat_heat_kernel
"""

from __future__ import annotations

import mpmath as mp

mp.mp.dps = 60


def heat_char_sum(phi, tau, nmax=None):
    """K(phi; s) by the character sum (repo conventions)."""
    if nmax is None:
        # s^{C(n)} = e^{-tau((n+1)^2-1)}: truncate when negligible
        nmax = int(mp.ceil(mp.sqrt(160 / tau))) + 4
    s = mp.e ** (-tau)
    acc = mp.mpf(0)
    for n in range(0, nmax + 1):
        acc += (n + 1) * s ** (n * (n + 2)) \
            * mp.sin((n + 1) * phi) / mp.sin(phi)
    return acc


def heat_image_sum(phi, tau, jmax=None):
    """K(phi; s) by the exact flat (Gaussian image) representation."""
    if jmax is None:
        jmax = int(mp.ceil(mp.sqrt(160 * 4 * tau) / mp.pi)) + 3
    pref = mp.e ** tau * mp.sqrt(mp.pi) / (4 * tau ** mp.mpf("1.5")) \
        / mp.sin(phi)
    acc = mp.mpf(0)
    for j in range(-jmax, jmax + 1):
        x = phi - 2 * mp.pi * j
        acc += x * mp.e ** (-(x * x) / (4 * tau))
    return pref * acc


def identity_gate(digits=40):
    """The image formula equals the character sum to `digits` digits
    across a grid of couplings and class angles.

    At small tau and large phi the kernel is ~ e^{-phi^2/(4 tau)}
    while the character-sum terms are O(1): the character sum loses
    ~ phi^2/(4 tau ln 10) digits to cancellation, so the working
    precision is raised per grid point to keep the COMPARISON at
    `digits` significant digits of the value."""
    worst = mp.mpf(0)
    for tau in (mp.mpf("0.02"), mp.mpf("0.1"), mp.mpf("0.5"),
                mp.mpf("1.5")):
        for phi in (mp.mpf("0.3"), mp.mpf("1.0"), mp.mpf("2.0"),
                    mp.mpf("2.9")):
            cancel = int(phi * phi / (4 * tau) / mp.log(10)) + 1
            with mp.workdps(digits + cancel + 50):
                # the character tail must be small RELATIVE to the
                # (possibly exponentially small) value: n e^{-tau n^2}
                # < 1e-digits * e^{-phi^2/(4 tau)} needs
                # tau n^2 > digits ln10 + phi^2/(4 tau) + margin
                need = (digits * mp.log(10) + phi * phi / (4 * tau)
                        + 60)
                nmax = int(mp.ceil(mp.sqrt(need / tau))) + 10
                a = heat_char_sum(phi, tau, nmax=nmax)
                b = heat_image_sum(phi, tau)
                rel = abs(a - b) / abs(a)
            worst = max(worst, rel)
    return worst < mp.mpf(10) ** (-digits), worst


def normalization_gate(digits=35):
    """Haar integral of K is 1 in these conventions:
    (2/pi) int_0^pi K(phi) sin^2(phi) dphi = 1  (Weyl measure),
    via the image representation."""
    worst = mp.mpf(0)
    for tau in (mp.mpf("0.05"), mp.mpf("0.4"), mp.mpf("1.0")):
        val = mp.quad(lambda p: heat_image_sum(p, tau)
                      * mp.sin(p) ** 2, [mp.mpf("1e-30"), mp.pi])
        rel = abs(val * 2 / mp.pi - 1)
        worst = max(worst, rel)
    return worst < mp.mpf(10) ** (-digits), worst


def character_projection_gate(digits=30):
    """(2/pi) int K(phi) chi_n(phi) sin^2 phi dphi = d_n s^{C(n)}:
    the image representation reproduces every character coefficient
    (spot-checked n = 1, 2, 3 at two couplings)."""
    worst = mp.mpf(0)
    for tau in (mp.mpf("0.1"), mp.mpf("0.7")):
        s = mp.e ** (-tau)
        for n in (1, 2, 3):
            val = mp.quad(
                lambda p: heat_image_sum(p, tau)
                * (mp.sin((n + 1) * p) / mp.sin(p)) * mp.sin(p) ** 2,
                [mp.mpf("1e-30"), mp.pi]) * 2 / mp.pi
            want = (n + 1) * s ** (n * (n + 2))
            rel = abs(val - want) / want
            worst = max(worst, rel)
    return worst < mp.mpf(10) ** (-digits), worst


def main() -> None:
    print("SU(2) exact flat (image-sum) heat-kernel representation — "
          "verification gates")
    ok, w = identity_gate()
    print(f"  identity gate (char sum == image sum, 16 grid points): "
          f"{'PASSED' if ok else 'FAILED'}  worst rel = {mp.nstr(w, 3)}")
    ok2, w2 = normalization_gate()
    print(f"  Haar normalization gate: {'PASSED' if ok2 else 'FAILED'}"
          f"  worst rel = {mp.nstr(w2, 3)}")
    ok3, w3 = character_projection_gate()
    print(f"  character projection gate (n = 1..3): "
          f"{'PASSED' if ok3 else 'FAILED'}  worst rel = {mp.nstr(w3, 3)}")
    assert ok and ok2 and ok3


if __name__ == "__main__":
    main()
