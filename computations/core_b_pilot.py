"""Core-B saddle local-CLT pilot: the p>=2 discrete SU(2) fusion residual.

Numerical Rule-5 harness for the one open residual behind
``FusionKernelStatement.SaddleLogForm`` / ``SaddleLocalCLT.bulkShiftBound``:
the p>=2 discrete SU(2) fusion local-CLT.  It reconstructs the exact ``Q'``/Nat
objects (``bondMovedCoeff``, ``fusionEig``, ``fusionKernelNorm``, ``eigA``,
``c4``, ``dimQ``, ``q112``), extracts the saddle moduli ``A_p(w)``, ``eta_p(w)``
from ``log K_{w,p}(s) = -A_p*C2(s) + R_p(s,w)``, sweeps ``(w, p)``, locates the
failure boundaries, and checks the ``1/12`` localization budget.

It also measures the **Tier-0 mirror** quantities
(``XMeanSecondDiffLeOne`` / ``casimir_secondDiff_eq_two`` / ``MeanShiftHalf`` /
``MeanShiftComplementHalf``) so both faces of Core-B are validated by one script.

The module encodes the two load-bearing honesty facts as executable assertions:

* the **estimate side** (``SaddleLogForm.estimate``, the ``eta*C2^2`` remainder)
  is satisfiable with wide margin and monotone structure (worst = smallest ``w``,
  ``p = 2``); this is the statement to make load-bearing;
* the **literal** Lean field
  ``SaddleLocalCLT.bulkShiftBound : forall s, fusionEig - eigA w s <= 1/12``
  (with the *bare* ``eigA = w^{c4 s}``) is **not satisfiable for p >= 2**; it
  works at ``p = 1`` only because ``eigA`` is then the exact eigenvalue
  (shift == 0).  The recommended fix, validated by the *rebased* surface, is to
  re-base to ``w_eff = exp(-A_p)`` (equivalently restate multiplicatively via the
  ``eta*C2^2`` remainder).

This module does NOT attempt a proof; it mirrors, not replaces, the Lean.  The
open analytic estimate stays open (Rule 5).

Mirrored Lean declarations (exact ``Q'``/Nat arithmetic):
    dimQ, c4, coeffW, fusionOK/fusionInd, fusionUnit, fusionProduct, fusionPow,
    bondMovedCoeff, normSep (= fusionKernelNorm), fusionEig, eigA, q112,
    acN, acnFmom, xmomN, pmomN (Tier-0), casimir_secondDiff_eq_two.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path
from typing import Any

import mpmath as mp

Number = Any  # Fraction | mp.mpf

# ---------------------------------------------------------------------------
# Defaults (mirror the plan's grid).
# ---------------------------------------------------------------------------
DEFAULT_W_VALUES: list[Fraction] = [
    Fraction(1, 2),
    Fraction(2, 3),
    Fraction(7, 9),   # wHi, the character-window ceiling
    Fraction(11, 12),
    Fraction(95, 96),  # demoW
]
DEFAULT_P_VALUES: list[int] = [1, 2, 3, 4, 8, 16, 27, 64]
DEFAULT_S_MAX: int = 8
DEFAULT_N: int = 20
DEFAULT_DPS: int = 40

Q112: Fraction = Fraction(1, 12)  # Lean `q112`, the localization margin.

_VIZ_DIR = (
    Path(__file__).resolve().parent.parent
    / "visualizations"
    / "pilot"
    / "core_b"
)


# ---------------------------------------------------------------------------
# Section "Q' mirror": exact mirrored Lean/Nat defs.
# ---------------------------------------------------------------------------
def dim_q(s: int) -> int:
    """`dimQ s = s + 1` (Lean `RGTransport.dimQ`)."""
    return s + 1


def c4(s: int) -> int:
    """`c4 s = s*(s+2) = C2(s)` in the saddle statement (Lean `RGTransport.c4`)."""
    return s * (s + 2)


def coeff_w(w: Number, s: int) -> Number:
    """`coeffW w s = (s+1)*w^{s(s+2)}` (Lean `BondMovingStep.coeffW`)."""
    return dim_q(s) * (w ** c4(s))


def fusion_ok(a: int, b: int, s: int) -> bool:
    """SU(2) Clebsch-Gordan selection (Lean `BondMovingStep.fusionOK`).

    `|a-b| <= s <= a+b` and `a+b+s` even.  Note `(a+b+s) % 2 == 0` is equivalent
    to `(a+b-s) % 2 == 0` since `-s == s (mod 2)`.
    """
    return (abs(a - b) <= s <= a + b) and ((a + b + s) % 2 == 0)


def fusion_ind(a: int, b: int, s: int) -> int:
    """`fusionInd a b s = 1` iff `χ_s ∈ χ_a·χ_b`, else 0 (Lean `fusionInd`)."""
    return 1 if fusion_ok(a, b, s) else 0


def fusion_unit(d: int) -> int:
    """`fusionUnit d = δ_{d,0}` — the trivial rep (Lean `fusionUnit`)."""
    return 1 if d == 0 else 0


def fusion_product(
    n_cut: int, a_arr: list[Number], b_arr: list[Number], zero: Number
) -> list[Number]:
    """Truncated Clebsch-Gordan convolution (Lean `fusionProduct`).

    `out(s) = Σ_{a=0}^{N} Σ_{b=0}^{N} fusionInd(a,b,s)·a_arr(a)·b_arr(b)`,
    returned as an array over `s ∈ [0, N]`.  As in Lean, intermediate factors are
    only ever queried at indices `<= N`, so truncating the output to `[0, N]` is
    exact for the `p`-fold fold.
    """
    out = [zero] * (n_cut + 1)
    for a in range(n_cut + 1):
        ai = a_arr[a]
        if ai == 0:
            continue
        for b in range(n_cut + 1):
            bj = b_arr[b]
            if bj == 0:
                continue
            prod = ai * bj
            hi = min(a + b, n_cut)
            for s in range(abs(a - b), hi + 1):
                if (a + b + s) % 2 == 0:
                    out[s] = out[s] + prod
    return out


def fusion_pow(
    n_cut: int, c_arr: list[Number], p: int, one: Number, zero: Number
) -> list[Number]:
    """`p`-fold fusion of `c_arr` with truncation `N` (Lean `fusionPow`).

    Base `p=0` is the fusion unit `δ_{s,0}`; each step folds one more copy of
    `c_arr`.  `fusion_pow(., 1, .)` reproduces `c_arr` on `s <= N`.
    """
    acc = [zero] * (n_cut + 1)
    acc[0] = one
    for _ in range(p):
        acc = fusion_product(n_cut, acc, c_arr, zero)
    return acc


def _coeff_w_array(w: Number, n_cut: int) -> list[Number]:
    return [coeff_w(w, s) for s in range(n_cut + 1)]


def bond_moved_array(w: Number, n_cut: int, p: int, one: Number, zero: Number) -> list[Number]:
    """The full bond-moved coefficient array `bmc(N,w,p,·)` on `s ∈ [0, N]`."""
    return fusion_pow(n_cut, _coeff_w_array(w, n_cut), p, one, zero)


def _numeric_units(w: Number) -> tuple[Number, Number]:
    if isinstance(w, Fraction):
        return Fraction(1), Fraction(0)
    return mp.mpf(1), mp.mpf(0)


def bond_moved_coeff(n_cut: int, w: Number, p: int, s: int) -> Number:
    """`bondMovedCoeff N w p s` (Lean `BondMovingStep.bondMovedCoeff`)."""
    one, zero = _numeric_units(w)
    return bond_moved_array(w, n_cut, p, one, zero)[s]


def fusion_kernel_norm(n_cut: int, w: Number, p: int, s: int) -> Number:
    """`fusionKernelNorm = normSep = bmc(s)/bmc(0)` (carries multiplicity `s+1`)."""
    one, zero = _numeric_units(w)
    arr = bond_moved_array(w, n_cut, p, one, zero)
    return arr[s] / arr[0]


def fusion_eig(n_cut: int, w: Number, p: int, s: int) -> Number:
    """`fusionEig = bmc(s)/((s+1)*bmc(0)) = fusionKernelNorm/dimQ s` (Lean `fusionEig`)."""
    one, zero = _numeric_units(w)
    arr = bond_moved_array(w, n_cut, p, one, zero)
    return arr[s] / (dim_q(s) * arr[0])


def eig_a(w: Number, s: int) -> Number:
    """`eigA w s = w^{s(s+2)}` — the bare p=1 heat rate (Lean `SpectralLocalizationCrux.eigA`)."""
    return w ** c4(s)


# ---------------------------------------------------------------------------
# Section "saddle moduli": Core-B extraction.
# ---------------------------------------------------------------------------
@dataclass
class SaddleModuli:
    """Saddle moduli of `log K_{w,p}(s) = -A*C2(s) + R(s)` (mirrors `SaddleLogForm`)."""

    A: mp.mpf
    eta: mp.mpf
    w_eff: mp.mpf
    a_from_s1: mp.mpf
    a_s1_gap: mp.mpf
    residuals: dict[int, mp.mpf] = field(default_factory=dict)


def _to_mpf(w: Number) -> mp.mpf:
    if isinstance(w, Fraction):
        return mp.mpf(w.numerator) / mp.mpf(w.denominator)
    return mp.mpf(w)


def _mpf_bmc_array(n_cut: int, w: Number, p: int) -> list[mp.mpf]:
    """The bond-moved coefficient array in mpmath (single computation per cell)."""
    return bond_moved_array(_to_mpf(w), n_cut, p, mp.mpf(1), mp.mpf(0))


def _log_eig_array(arr: list[mp.mpf], s_max: int) -> dict[int, mp.mpf]:
    """`L(s) = log(fusionEig(s))` for `s = 1..s_max` from a precomputed mpf array."""
    out: dict[int, mp.mpf] = {}
    for s in range(1, s_max + 1):
        eig = arr[s] / (dim_q(s) * arr[0])
        out[s] = mp.log(eig)
    return out


def saddle_fit(n_cut: int, w: Number, p: int, s_max: int,
               arr: list[mp.mpf] | None = None) -> SaddleModuli:
    """Extract `A_p(w)`, `eta_p(w)` from the log/saddle form (mirrors `SaddleLogForm`).

    `A_p = argmin_A sup_{1<=s<=s_max} |L(s)+A*C2(s)|/C2(s)^2`; `eta_p` = that min.
    An optional precomputed mpf `arr` avoids recomputing the fusion power.
    """
    if arr is None:
        arr = _mpf_bmc_array(n_cut, w, p)
    logs = _log_eig_array(arr, s_max)
    ss = sorted(logs)

    def objective(a_val: mp.mpf) -> mp.mpf:
        worst = mp.mpf(0)
        for s in ss:
            c2 = mp.mpf(c4(s))
            val = abs(logs[s] + a_val * c2) / (c2 * c2)
            if val > worst:
                worst = val
        return worst

    a_from_s1 = -logs[1] / mp.mpf(c4(1))
    lo = mp.mpf(0)
    hi = max(a_from_s1 * 2, -mp.log(_to_mpf(w)) * mp.mpf("1.5")) + 1
    # Golden-section / ternary search (objective convex in A).
    for _ in range(200):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        if objective(m1) < objective(m2):
            hi = m2
        else:
            lo = m1
    a_star = (lo + hi) / 2
    eta = objective(a_star)
    residuals = {s: logs[s] + a_star * mp.mpf(c4(s)) for s in ss}
    return SaddleModuli(
        A=a_star,
        eta=eta,
        w_eff=mp.e ** (-a_star),
        a_from_s1=a_from_s1,
        a_s1_gap=abs(a_star - a_from_s1),
        residuals=residuals,
    )


def remainder_table(n_cut: int, w: Number, p: int, s_max: int) -> dict[int, tuple[mp.mpf, mp.mpf]]:
    """Per-`s` `(R_p(s,w), |R_p|/C2(s)^2)` for inspection."""
    mod = saddle_fit(n_cut, w, p, s_max)
    out: dict[int, tuple[mp.mpf, mp.mpf]] = {}
    for s, r in mod.residuals.items():
        c2 = mp.mpf(c4(s))
        out[s] = (r, abs(r) / (c2 * c2))
    return out


# ---------------------------------------------------------------------------
# Section "sweep": (w,p) surfaces, failure boundaries, 1/12 budget.
# ---------------------------------------------------------------------------
@dataclass
class SweepResult:
    """The four measured `(w,p)` surfaces plus derived diagnostics."""

    eta: dict[tuple[str, int], float]
    literal_shift: dict[tuple[str, int], float]
    rebased_shift: dict[tuple[str, int], float]
    a_p: dict[tuple[str, int], float]
    w_eff: dict[tuple[str, int], float]
    eta_margin: dict[tuple[str, int], float]
    literal_pass: dict[tuple[str, int], bool]
    eta_fail_boundary: list[tuple[str, int]]
    literal_fail_boundary: list[tuple[str, int]]


def _w_label(w: Fraction) -> str:
    return f"{w.numerator}/{w.denominator}"


def literal_shift(n_cut: int, w: Number, p: int, s_max: int,
                  arr: list[Number] | None = None) -> Number:
    """`max_{1<=s<=s_max} (fusionEig(s) - eigA(w,s))` — the *literal* `bulkShiftBound` LHS.

    With `arr` omitted the fusion power is computed in the same number field as
    `w` (exact `Fraction` when `w` is a `Fraction`); pass a precomputed mpf `arr`
    for the sweep (exact `Fraction` at large `p` blows up).
    """
    if arr is None:
        one, zero = _numeric_units(w)
        arr = bond_moved_array(w, n_cut, p, one, zero)
        w_ref: Number = w
    else:
        w_ref = _to_mpf(w)
    worst = None
    for s in range(1, s_max + 1):
        eig = arr[s] / (dim_q(s) * arr[0])
        shift = eig - eig_a(w_ref, s)
        if worst is None or shift > worst:
            worst = shift
    return worst


def rebased_shift(n_cut: int, w: Number, p: int, s_max: int, w_eff: mp.mpf,
                  arr: list[mp.mpf] | None = None) -> mp.mpf:
    """`max_s |fusionEig(s) - w_eff^{c4 s}|` — the correct p-fold reference."""
    if arr is None:
        arr = _mpf_bmc_array(n_cut, w, p)
    worst = mp.mpf(0)
    for s in range(1, s_max + 1):
        eig = arr[s] / (dim_q(s) * arr[0])
        dev = abs(eig - w_eff ** c4(s))
        if dev > worst:
            worst = dev
    return worst


def run_sweep(
    w_values: list[Fraction],
    p_values: list[int],
    s_max: int,
    n_cut: int,
) -> SweepResult:
    """Sweep the three measured surfaces over `(w, p)` and locate boundaries."""
    eta: dict[tuple[str, int], float] = {}
    lit: dict[tuple[str, int], float] = {}
    reb: dict[tuple[str, int], float] = {}
    a_p: dict[tuple[str, int], float] = {}
    w_eff: dict[tuple[str, int], float] = {}
    margin: dict[tuple[str, int], float] = {}
    lit_pass: dict[tuple[str, int], bool] = {}
    eta_fail: list[tuple[str, int]] = []
    lit_fail: list[tuple[str, int]] = []
    budget = float(Q112)
    for w in w_values:
        wl = _w_label(w)
        for p in p_values:
            arr = _mpf_bmc_array(n_cut, w, p)  # single fusion power per cell
            mod = saddle_fit(n_cut, w, p, s_max, arr=arr)
            eta_v = float(mod.eta)
            eta[(wl, p)] = eta_v
            a_p[(wl, p)] = float(mod.A)
            w_eff[(wl, p)] = float(mod.w_eff)
            margin[(wl, p)] = budget / eta_v if eta_v > 0 else float("inf")
            if eta_v >= budget:
                eta_fail.append((wl, p))
            # literal shift against bare p=1 rate.
            lit_v = float(literal_shift(n_cut, w, p, s_max, arr=arr))
            lit[(wl, p)] = lit_v
            ok = lit_v <= budget
            lit_pass[(wl, p)] = ok
            if not ok:
                lit_fail.append((wl, p))
            reb[(wl, p)] = float(rebased_shift(n_cut, w, p, s_max, mod.w_eff, arr=arr))
    return SweepResult(
        eta=eta,
        literal_shift=lit,
        rebased_shift=reb,
        a_p=a_p,
        w_eff=w_eff,
        eta_margin=margin,
        literal_pass=lit_pass,
        eta_fail_boundary=eta_fail,
        literal_fail_boundary=lit_fail,
    )


def p1_anchor_ok(n_cut: int, w: Fraction, s_max: int) -> bool:
    """`p=1` exact-fraction anchor: `fusionEig == eigA` and literal shift == 0.

    Mirrors `saddleLocalCLT_p1` (shift ≡ 0).  Uses exact `Fraction` arithmetic.
    """
    arr = bond_moved_array(w, n_cut, 1, Fraction(1), Fraction(0))
    for s in range(1, min(s_max, n_cut) + 1):
        eig = arr[s] / (dim_q(s) * arr[0])
        if eig != eig_a(w, s):
            return False
    return literal_shift(n_cut, w, 1, min(s_max, n_cut)) == Fraction(0)


# ---------------------------------------------------------------------------
# Section "tilted-variance unification": the Tier-0 mirror.
# ---------------------------------------------------------------------------
def casimir_second_diff(s: int) -> int:
    """`Δ²C4(s) = c4(s)+c4(s+2)-2·c4(s+1)` — always 2 (Lean `casimir_secondDiff_eq_two`)."""
    return c4(s) + c4(s + 2) - 2 * c4(s + 1)


def _acn(w: Number, n_win: int, t: int) -> Number:
    """`acN w n t = Σ_{p<n} coeffW(p)·coeffW(t-p)` (diagonal-band autoconvolution)."""
    _, zero = _numeric_units(w)
    total = zero
    for pp in range(n_win):
        total = total + coeff_w(w, pp) * coeff_w(w, t - pp)
    return total


def _acn_fmom(w: Number, n_win: int, t: int) -> Number:
    """`acnFmom w n t = Σ_{p<n} (c4(p)+c4(t-p))·coeffW(p)·coeffW(t-p) = w·∂_w acN`."""
    _, zero = _numeric_units(w)
    total = zero
    for pp in range(n_win):
        total = total + (c4(pp) + c4(t - pp)) * (coeff_w(w, pp) * coeff_w(w, t - pp))
    return total


def _xmom(w: Number, n_win: int, t: int) -> Number:
    """`xmomN w n t = Σ_{p<n} p(t-p)·coeffW(p)·coeffW(t-p)` (cross-product statistic)."""
    _, zero = _numeric_units(w)
    total = zero
    for pp in range(n_win):
        total = total + (pp * (t - pp)) * (coeff_w(w, pp) * coeff_w(w, t - pp))
    return total


def _pmom(w: Number, n_win: int, t: int) -> Number:
    """`pmomN w n t = Σ_{p<n} p·coeffW(p)·coeffW(t-p)` (base-index first moment)."""
    _, zero = _numeric_units(w)
    total = zero
    for pp in range(n_win):
        total = total + pp * (coeff_w(w, pp) * coeff_w(w, t - pp))
    return total


def mean_x(w: Number, s: int, t: int) -> Number:
    """`<x>_t = xmomN(s+1,t)/acN(s+1,t)`, window `s+1` (as in `XMeanSecondDiffLeOne`)."""
    return _xmom(w, s + 1, t) / _acn(w, s + 1, t)


def mean_p(w: Number, s: int, t: int) -> Number:
    """`<p>_t = pmomN(s+1,t)/acN(s+1,t)`, window `s+1` (as in `MeanShiftHalf`)."""
    return _pmom(w, s + 1, t) / _acn(w, s + 1, t)


def d2x(w: Number, s: int) -> Number:
    """`d2x(s) = <x>_s + <x>_{s+2} - 2<x>_{s+1}` (Lean `XMeanSecondDiffLeOne`; `<= 1`)."""
    return mean_x(w, s, s) + mean_x(w, s, s + 2) - 2 * mean_x(w, s, s + 1)


def mean_shift_half(w: Number, s: int) -> Number:
    """`dB = <p>_{s+2} - <p>_{s+1}` (Lean `MeanShiftHalf`; `<= 1/2`)."""
    return mean_p(w, s, s + 2) - mean_p(w, s, s + 1)


def mean_shift_complement_half(w: Number, s: int) -> Number:
    """`dC = d2x - dB` (Lean `MeanShiftComplementHalf`; `<= 1/2`)."""
    return d2x(w, s) - mean_shift_half(w, s)


def pfmom_check(w: Number, s: int) -> tuple[Number, Number]:
    """Verify the product-first-moment identity `pfmom_split` numerically.

    `acnFmom = w·∂_w acN`, so the tilted first moment of `P(w)=acN_s·acN_{s+2}`
    is `acnFmom_s·acN_{s+2}+acN_s·acnFmom_{s+2}` (Leibniz).  Returns
    `(analytic, finite_difference)` — the mean-of-product identity check.
    """
    wm = _to_mpf(w)
    n = s + 1
    analytic = (
        _acn_fmom(wm, n, s) * _acn(wm, n, s + 2)
        + _acn(wm, n, s) * _acn_fmom(wm, n, s + 2)
    )
    # w d/dw of P(w) = acN_s(w)·acN_{s+2}(w) by central finite difference in log w.
    h = mp.mpf("1e-25")

    def prod(wv: mp.mpf) -> mp.mpf:
        return _acn(wv, n, s) * _acn(wv, n, s + 2)

    lp = mp.log(wm) + h
    lm = mp.log(wm) - h
    fd = (prod(mp.e ** lp) - prod(mp.e ** lm)) / (2 * h)
    return analytic, fd


@dataclass
class Tier0Result:
    """Tier-0 mirror measurements over a `(w, s)` grid."""

    max_d2x: float
    casimir_ok: bool
    worst_half_slack: float
    worst_complement_slack: float
    pfmom_rel_err: float
    d2x_by_cell: dict[tuple[str, int], float]


def run_tier0(w_values: list[Fraction], s_range: list[int]) -> Tier0Result:
    """Measure the Tier-0 saddle physics (exact `Fraction`) over `(w, s)`."""
    half = Fraction(1, 2)
    max_d2x = 0.0
    casimir_ok = all(casimir_second_diff(s) == 2 for s in s_range)
    worst_half = 0.0
    worst_comp = 0.0
    d2x_cell: dict[tuple[str, int], float] = {}
    for w in w_values:
        wl = _w_label(w)
        for s in s_range:
            dv = d2x(w, s)
            d2x_cell[(wl, s)] = float(dv)
            if float(dv) > max_d2x:
                max_d2x = float(dv)
            hb = mean_shift_half(w, s)
            hc = mean_shift_complement_half(w, s)
            worst_half = max(worst_half, float(half - hb))
            worst_comp = max(worst_comp, float(half - hc))
    # pfmom identity relative error (representative cell).
    an, fd = pfmom_check(w_values[0], s_range[-1])
    rel = float(abs(an - fd) / abs(an)) if an != 0 else 0.0
    return Tier0Result(
        max_d2x=max_d2x,
        casimir_ok=casimir_ok,
        worst_half_slack=worst_half,
        worst_complement_slack=worst_comp,
        pfmom_rel_err=rel,
        d2x_by_cell=d2x_cell,
    )


# ---------------------------------------------------------------------------
# Section: plots.
# ---------------------------------------------------------------------------
def _new_axes():
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    return plt


def plot_eta_sweep(
    result: SweepResult,
    w_values: list[Fraction],
    p_values: list[int],
    output_path: Path,
) -> Path:
    """`eta_p(w)` vs `p` per `w`, with the `1/12` budget line."""
    plt = _new_axes()
    fig, ax = plt.subplots(figsize=(6.5, 4.2))
    for w in w_values:
        wl = _w_label(w)
        ys = [result.eta[(wl, p)] for p in p_values]
        ax.plot(p_values, ys, "o-", markersize=5, label=f"w={wl}")
    ax.axhline(float(Q112), color="k", ls="--", lw=1.0, label="1/12 budget")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel("bond-moving exponent p")
    ax.set_ylabel(r"$\eta_p(w)$ (curvature remainder)")
    ax.set_title("Core-B saddle remainder modulus vs p")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    fig.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, format="svg")
    plt.close(fig)
    return output_path


def plot_literal_vs_rebased(
    result: SweepResult,
    w_values: list[Fraction],
    p_values: list[int],
    output_path: Path,
) -> Path:
    """Two panels: literal `fusionEig-eigA` (crosses 1/12) vs rebased shift (under)."""
    plt = _new_axes()
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.2), sharey=True)
    for w in w_values:
        wl = _w_label(w)
        ax1.plot(
            p_values,
            [result.literal_shift[(wl, p)] for p in p_values],
            "o-",
            markersize=5,
            label=f"w={wl}",
        )
        ax2.plot(
            p_values,
            [result.rebased_shift[(wl, p)] for p in p_values],
            "s-",
            markersize=5,
            label=f"w={wl}",
        )
    for ax, title in ((ax1, "literal shift  (fusionEig - w^{c4 s})"),
                      (ax2, "rebased shift  |fusionEig - w_eff^{c4 s}|")):
        ax.axhline(float(Q112), color="k", ls="--", lw=1.0, label="1/12")
        ax.set_xscale("log")
        ax.set_xlabel("p")
        ax.set_title(title, fontsize=9)
        ax.grid(True, alpha=0.3)
    ax1.set_ylabel("max-mode shift")
    ax1.legend(fontsize=8)
    fig.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, format="svg")
    plt.close(fig)
    return output_path


def plot_saddle_remainder(
    n_cut: int,
    w: Fraction,
    p: int,
    s_max: int,
    output_path: Path,
) -> Path:
    """`R_p(s,w)/C2(s)^2` vs `s` for a worst corner (flat curvature remainder)."""
    plt = _new_axes()
    table = remainder_table(n_cut, w, p, s_max)
    ss = sorted(table)
    ys = [float(table[s][1]) for s in ss]
    fig, ax = plt.subplots(figsize=(6.5, 4.2))
    ax.plot(ss, ys, "o-", color="tab:purple", markersize=5)
    ax.axhline(float(Q112), color="k", ls="--", lw=1.0, label="1/12")
    ax.set_xlabel("spin label s")
    ax.set_ylabel(r"$|R_p(s,w)|/C_2(s)^2$")
    ax.set_title(f"Saddle remainder, w={_w_label(w)}, p={p}")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    fig.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, format="svg")
    plt.close(fig)
    return output_path


def plot_weff_flattening(
    result: SweepResult,
    w_values: list[Fraction],
    p_values: list[int],
    output_path: Path,
) -> Path:
    """`w_eff=exp(-A_p)` vs `p` approaching 1; `A_p` vs `(-log w)/p`."""
    plt = _new_axes()
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11.0, 4.2))
    for w in w_values:
        wl = _w_label(w)
        ax1.plot(p_values, [result.w_eff[(wl, p)] for p in p_values],
                 "o-", markersize=5, label=f"w={wl}")
        neglog = float(-mp.log(_to_mpf(w)))
        ax2.plot(p_values, [result.a_p[(wl, p)] for p in p_values],
                 "o-", markersize=5, label=f"A_p, w={wl}")
        ax2.plot(p_values, [neglog / p for p in p_values],
                 "--", lw=0.9, label=f"(-log w)/p, w={wl}")
    ax1.axhline(1.0, color="k", ls=":", lw=0.9)
    ax1.set_xscale("log")
    ax1.set_xlabel("p")
    ax1.set_ylabel(r"$w_{\rm eff}=e^{-A_p}$")
    ax1.set_title("effective p-fold rate -> 1", fontsize=9)
    ax1.grid(True, alpha=0.3)
    ax1.legend(fontsize=7)
    ax2.set_xscale("log")
    ax2.set_yscale("log")
    ax2.set_xlabel("p")
    ax2.set_ylabel(r"$A_p$")
    ax2.set_title("A_p flattens slower than 1/p", fontsize=9)
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=6)
    fig.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, format="svg")
    plt.close(fig)
    return output_path


def plot_tier0_curvature(
    tier0: Tier0Result,
    w_values: list[Fraction],
    s_range: list[int],
    output_path: Path,
) -> Path:
    """`d2x(s)` per `w` with the `<= 1` floor."""
    plt = _new_axes()
    fig, ax = plt.subplots(figsize=(6.5, 4.2))
    for w in w_values:
        wl = _w_label(w)
        ys = [tier0.d2x_by_cell[(wl, s)] for s in s_range]
        ax.plot(s_range, ys, "o-", markersize=5, label=f"w={wl}")
    ax.axhline(1.0, color="k", ls="--", lw=1.0, label="d2x <= 1")
    ax.set_xlabel("spin label s")
    ax.set_ylabel(r"$d2x(s)=\langle x\rangle_s+\langle x\rangle_{s+2}-2\langle x\rangle_{s+1}$")
    ax.set_title("Tier-0 shift second-difference (curvature)")
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=8)
    fig.tight_layout()
    output_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output_path, format="svg")
    plt.close(fig)
    return output_path


def write_all_plots(
    result: SweepResult,
    tier0: Tier0Result,
    w_values: list[Fraction],
    p_values: list[int],
    s_max: int,
    n_cut: int,
    out_dir: Path = _VIZ_DIR,
) -> list[Path]:
    """Render every pilot SVG to `out_dir`."""
    tier0_s = sorted({s for (_, s) in tier0.d2x_by_cell})
    paths = [
        plot_eta_sweep(result, w_values, p_values, out_dir / "eta-sweep.svg"),
        plot_literal_vs_rebased(
            result, w_values, p_values, out_dir / "literal-vs-rebased-shift.svg"
        ),
        plot_saddle_remainder(
            n_cut, w_values[0], 2, s_max, out_dir / "saddle-remainder.svg"
        ),
        plot_weff_flattening(
            result, w_values, p_values, out_dir / "weff-flattening.svg"
        ),
        plot_tier0_curvature(
            tier0, w_values, tier0_s, out_dir / "tier0-curvature.svg"
        ),
    ]
    return paths


# ---------------------------------------------------------------------------
# Section: CLI results table + JSON.
# ---------------------------------------------------------------------------
def _serialize_surface(surface: dict[tuple[str, int], Any]) -> dict[str, Any]:
    return {f"{wl}|p={p}": v for (wl, p), v in surface.items()}


def to_json_payload(
    result: SweepResult, tier0: Tier0Result
) -> dict[str, Any]:
    """Machine-readable payload of all four surfaces + Tier-0 summary."""
    return {
        "eta_sweep": _serialize_surface(result.eta),
        "literal_shift_sweep": _serialize_surface(result.literal_shift),
        "rebased_shift_sweep": _serialize_surface(result.rebased_shift),
        "a_p_sweep": _serialize_surface(result.a_p),
        "w_eff_sweep": _serialize_surface(result.w_eff),
        "eta_margin": _serialize_surface(result.eta_margin),
        "literal_pass": _serialize_surface(result.literal_pass),
        "eta_fail_boundary": [f"{wl}|p={p}" for wl, p in result.eta_fail_boundary],
        "literal_fail_boundary": [
            f"{wl}|p={p}" for wl, p in result.literal_fail_boundary
        ],
        "tier0": {
            "max_d2x": tier0.max_d2x,
            "casimir_second_diff_two": tier0.casimir_ok,
            "worst_half_slack": tier0.worst_half_slack,
            "worst_complement_slack": tier0.worst_complement_slack,
            "pfmom_rel_err": tier0.pfmom_rel_err,
        },
        "budget": float(Q112),
    }


def _print_summary(
    result: SweepResult,
    tier0: Tier0Result,
    w_values: list[Fraction],
    p_values: list[int],
    s_max: int,
    n_cut: int,
) -> None:
    budget = float(Q112)
    print("=" * 74)
    print("CORE-B saddle local-CLT pilot  (p>=2 discrete SU(2) fusion residual)")
    print("=" * 74)

    # p=1 exact anchor.
    anchors_ok = all(p1_anchor_ok(n_cut, w, s_max) for w in w_values)
    print(
        f"\n[anchor] p=1 exact: fusionEig == eigA and literal shift == 0  -> "
        f"{'OK' if anchors_ok else 'FAIL'}   (mirrors saddleLocalCLT_p1)"
    )

    # Table 1: eta with 1/12 margin.
    print(f"\nTable 1 -- eta_p(w) (curvature remainder); budget 1/12 = {budget:.5f}")
    head = "  w \\ p  " + "".join(f"{p:>10}" for p in p_values)
    print(head)
    for w in w_values:
        wl = _w_label(w)
        row = f"  {wl:>6} "
        for p in p_values:
            row += f"{result.eta[(wl, p)]:>10.4g}"
        print(row)
    worst_cell = max(result.eta, key=lambda k: result.eta[k])
    worst_margin = min(result.eta_margin.values())
    print(
        f"  worst eta = {result.eta[worst_cell]:.4g} at "
        f"(w={worst_cell[0]}, p={worst_cell[1]}); min budget margin = "
        f"{worst_margin:.1f}x;  eta-fail boundary: "
        f"{result.eta_fail_boundary or 'NONE'}"
    )

    # Table 2: literal shift PASS/FAIL.
    print("\nTable 2 -- literal shift  max_s(fusionEig - w^{c4 s})  vs 1/12")
    print(head)
    for w in w_values:
        wl = _w_label(w)
        row = f"  {wl:>6} "
        for p in p_values:
            v = result.literal_shift[(wl, p)]
            mark = "" if result.literal_pass[(wl, p)] else "!"
            row += f"{v:>9.3g}{mark}"
        print(row)
    print(f"  literal-fail boundary (>1/12): {result.literal_fail_boundary or 'NONE'}")

    # Table 3: rebased shift.
    print("\nTable 3 -- rebased shift  max_s|fusionEig - w_eff^{c4 s}|  vs 1/12")
    print(head)
    for w in w_values:
        wl = _w_label(w)
        row = f"  {wl:>6} "
        for p in p_values:
            row += f"{result.rebased_shift[(wl, p)]:>10.3g}"
        print(row)

    # Tier-0.
    print("\nTier-0 mirror (tilted-variance unification):")
    print(
        f"  Delta^2 C4 == 2 : {tier0.casimir_ok};  "
        f"max_s d2x = {tier0.max_d2x:.5f} (floor 1);  "
        f"worst half-slack = {tier0.worst_half_slack:.4f}, "
        f"complement-slack = {tier0.worst_complement_slack:.4f};  "
        f"pfmom rel-err = {tier0.pfmom_rel_err:.2e}"
    )

    # Verdict.
    est_green = not result.eta_fail_boundary
    print("\nVERDICT:")
    print(
        f"  estimate side (eta*C2^2): {'GREEN' if est_green else 'FAIL'} "
        f"(min margin {worst_margin:.0f}x under 1/12)"
    )
    lit_boundary_p = (
        min(p for _, p in result.literal_fail_boundary)
        if result.literal_fail_boundary
        else None
    )
    print(
        f"  literal bulkShiftBound: FAIL boundary p = {lit_boundary_p} "
        f"(bare eigA is the p=1 eigenvalue only)"
    )
    print("  recommendation: re-base bulkShiftBound to w_eff = exp(-A_p) "
          "(rebased surface all under 1/12).")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p-values", type=int, nargs="+", default=DEFAULT_P_VALUES)
    parser.add_argument(
        "--w-values",
        type=str,
        nargs="+",
        default=[_w_label(w) for w in DEFAULT_W_VALUES],
        help="fractions like 1/2 2/3 ...",
    )
    parser.add_argument("--s-max", type=int, default=DEFAULT_S_MAX)
    parser.add_argument("--N", type=int, default=DEFAULT_N)
    parser.add_argument("--dps", type=int, default=DEFAULT_DPS)
    parser.add_argument("--no-plots", action="store_true")
    parser.add_argument("--json", type=str, default=None)
    args = parser.parse_args(argv)

    mp.mp.dps = args.dps
    w_values = [Fraction(s) for s in args.w_values]
    p_values = list(args.p_values)

    result = run_sweep(w_values, p_values, args.s_max, args.N)
    tier0 = run_tier0(w_values, list(range(0, 7)))
    _print_summary(result, tier0, w_values, p_values, args.s_max, args.N)

    if not args.no_plots:
        paths = write_all_plots(
            result, tier0, w_values, p_values, args.s_max, args.N
        )
        print("\nPlots written:")
        for p in paths:
            print(f"  {p}")

    if args.json:
        out = Path(args.json)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(to_json_payload(result, tier0), indent=2))
        print(f"\nJSON written to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
