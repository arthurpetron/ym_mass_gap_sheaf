#!/usr/bin/env python3
"""
P7 β=2.95 Polyakov (torelon) sector vs 0++ — MC only, NOT proof.

Inputs (box paths):
  0++ : P7/P6 records runs/b2.95_L48x48_s8/data.bin, runs/b2.95_L32x48_s8/data.bin
        per meas: [plaq4, for 6 flow levels (rho=sqrt(6t)/8 = 0,.5,.75,1,1.25,1.5):
                   (E_s, for side in 7,8,9: 3 planes × Lt zero-momentum (1/2)Tr W_sxs)], (+6×6 global poly, L48 only)
  P   : polysec output poly_L{48,32}.bin (this folder): per cfg [E_s, lev × dir(3) × Lt zero-momentum P_d(t)],
        APE α=0.5 projected spatial smearing within each timeslice, levels 0,5,10,20,30.
Estimators: C(τ) = <O(t)O(t+τ)>_t (E1: minus sample <O>²; for P also UNSUBTRACTED, the center-symmetric
estimator since <P>=0 exactly in an ergodic ensemble). Periodic cosh effective mass. Jackknife over bins.
Torelon expectation: m_P = σL − π/(3L) (LO string) and NG ground state σL·sqrt(1 − 2π/(3σL²)), with
a√σ(β=2.95) from the a10b9ea4 module (two-loop from the FHK/UKQCD β=2.85 anchor). 0++ expectation μ·a√σ, μ=3.78(7) LTW04.
"""
from __future__ import annotations
import json, math, sys
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
RUNS = Path("/workspace/ymmc/p4_smoothed/runs")
PDIR = RUNS / "p7_polyakov_sector"
sys.path.insert(0, str(HERE.parent / "af_nome_asqrt"))
import af_nome_asqrt_schedule as sch  # a10b9ea4 single source of truth

MU = 3.78; MU_ERR = 0.07
BETA = 2.95; LT = 48
RHOS = [0.0, 0.5, 0.75, 1.0, 1.25, 1.5]; SIDES = [7, 8, 9]


def load_records(path: Path, reclen: int) -> tuple[dict, np.ndarray]:
    b = path.read_bytes(); h = b.index(b"\n") + 1
    hdr = json.loads(b[:h]); d = np.frombuffer(b[h:], dtype="<f8")
    n = d.size // reclen; return hdr, d[: n * reclen].reshape(n, reclen)


def ops_0pp(path: Path) -> np.ndarray:
    """Returns O[meas, lev, side, t] (mean over 3 planes)."""
    nlev, ns = len(RHOS), len(SIDES)
    base = 1 + nlev * (1 + ns * 3 * LT)
    size = path.stat().st_size
    for reclen in (base + nlev * 6, base):
        try:
            hdr, d = load_records(path, reclen)
            if (size - (len(json.dumps(hdr)) )) and d.shape[0] in (240,):
                break
        except Exception:
            continue
    out = np.empty((d.shape[0], nlev, ns, LT))
    for lv in range(nlev):
        o = 1 + lv * (1 + ns * 3 * LT) + 1
        for si in range(ns):
            blk = d[:, o + si * 3 * LT : o + (si + 1) * 3 * LT].reshape(-1, 3, LT)
            out[:, lv, si, :] = blk.mean(axis=1)
    return out


def ops_poly(path: Path) -> tuple[dict, np.ndarray]:
    b = path.read_bytes(); h = b.index(b"\n") + 1; hdr = json.loads(b[:h])
    nl = len(hdr["levels"]); lt = hdr["Lt"]; reclen = 1 + nl * 3 * lt
    d = np.frombuffer(b[h:], dtype="<f8"); n = d.size // reclen
    return hdr, d[: n * reclen].reshape(n, reclen)[:, 1:].reshape(n, nl, 3, lt)


def corr(x: np.ndarray, subtract: bool) -> np.ndarray:
    """x[n, ..., t] -> mean over configs of <x(t)x(t+τ)>_t, minus <x>^2 if subtract. Returns [..., τ]."""
    lt = x.shape[-1]
    c = np.stack([(x * np.roll(x, -tau, axis=-1)).mean(axis=-1) for tau in range(lt // 2 + 1)], axis=-1).mean(axis=0)
    if subtract:
        c = c - (x.mean(axis=(0, -1)) ** 2)[..., None]
    return c


def meff_cosh(c: np.ndarray, lt: int = LT) -> np.ndarray:
    """Periodic cosh effective mass from C(τ)/C(τ+1); NaN where undefined."""
    out = np.full(c.shape[:-1] + (c.shape[-1] - 1,), np.nan)
    for t in range(c.shape[-1] - 1):
        r = c[..., t] / c[..., t + 1]
        with np.errstate(all="ignore"):
            m0 = np.where(r > 1, np.log(r), np.nan)
        # Newton on cosh(m(t-T/2))/cosh(m(t+1-T/2)) = r
        m = m0.copy()
        for _ in range(60):
            a, bb = t - lt / 2, t + 1 - lt / 2
            with np.errstate(all="ignore"):
                f = np.cosh(m * a) / np.cosh(m * bb) - r
                df = (a * np.sinh(m * a) * np.cosh(m * bb) - bb * np.cosh(m * a) * np.sinh(m * bb)) / np.cosh(m * bb) ** 2
                m = np.where(np.isfinite(m), m - f / df, m)
        out[..., t] = np.where((m > 0) & (m < 5), m, np.nan)
    return out


def jackknife(x: np.ndarray, nbin: int, fn):
    """x[n, ...]: bin into nbin contiguous bins, delete-one jackknife of fn(subset)."""
    n = (x.shape[0] // nbin) * nbin; xs = x[:n].reshape(nbin, -1, *x.shape[1:])
    full = fn(x[:n])
    jk = np.stack([fn(np.concatenate([xs[i] for i in range(nbin) if i != k], axis=0)) for k in range(nbin)])
    with np.errstate(all="ignore"):
        err = np.sqrt((nbin - 1) * np.nanmean((jk - np.nanmean(jk, axis=0)) ** 2, axis=0))
    return full, err


def window_mean(mfn, lo: int, hi: int):
    """Wrap an m_eff function -> uncorrelated mean of m_eff over t in [lo, hi] (inclusive)."""
    def g(x):
        m = mfn(x)
        with np.errstate(all="ignore"):
            return np.nanmean(m[..., lo:hi + 1], axis=-1)
    return g


def fmt(v, e, p=3):
    if not np.isfinite(v): return "—"
    if not np.isfinite(e): return f"{v:.{p}f}(?)"
    return f"{v:.{p}f}({e:.{p}f})"


def main() -> None:
    asq, src, _ = sch.asqrt_at(BETA)
    a2s = asq * asq
    print(f"a√σ(β={BETA}) = {asq:.5f}  [{src}]  ⇒ a²σ = {a2s:.6f}")
    print(f"0++ expectation μ·a√σ = {MU*asq:.4f} ± {MU_ERR*asq:.4f} (μ=3.78(7) LTW04, continuum ratio)")
    for L in (32, 48):
        lo = a2s * L - math.pi / (3 * L)
        ng = a2s * L * math.sqrt(max(0.0, 1 - 2 * math.pi / (3 * a2s * L * L)))
        print(f"torelon L={L}: σL−π/(3L) = {lo:.4f}; NG = {ng:.4f}; σL = {a2s*L:.4f}; L√σ = {L*asq:.3f}")
    print()

    results = {}
    # ---- 0++ ----
    for L, fn in ((48, RUNS / "b2.95_L48x48_s8/data.bin"), (32, RUNS / "b2.95_L32x48_s8/data.bin")):
        O = ops_0pp(fn)  # [n, lev, side, t]
        print(f"=== 0++ Ls={L}: N={O.shape[0]} meas, bins of 10 (E1 subtracted) ===")
        f = lambda x: meff_cosh(corr(x, True))
        m, e = jackknife(O, O.shape[0] // 10, f)
        for lv in (2, 3, 4, 5):
            for si in range(3):
                print(f"  rho={RHOS[lv]:.2f} side {SIDES[si]}: m_eff(t=0..6) = " +
                      " ".join(fmt(m[lv, si, t], e[lv, si, t]) for t in range(7)))
        results[("0pp", L)] = (m, e)
        for lo, hi in ((2, 5), (3, 6), (4, 8)):
            pm, pe = jackknife(O, O.shape[0] // 10, window_mean(f, lo, hi))
            print(f"  plateau t∈[{lo},{hi}]: rho=1.25 s8 {fmt(pm[4,1],pe[4,1])}  rho=1.50 s8 {fmt(pm[5,1],pe[5,1])}  rho=1.50 s9 {fmt(pm[5,2],pe[5,2])}")
        print()

    # ---- Polyakov ----
    for L in (48, 32):
        fn = PDIR / f"poly_L{L}.bin"
        if not fn.exists():
            print(f"=== P Ls={L}: {fn.name} missing ==="); continue
        hdr, P = ops_poly(fn)
        n = P.shape[0]; nb = 16 if n >= 64 else max(4, n // 5)
        print(f"=== Polyakov Ls={L}: N={n} cfgs ({hdr['mode']}), levels={hdr['levels']}, jackknife bins={nb} ===")
        Pm = P.mean(axis=(0, 3)); Pabs = np.abs(P.mean(axis=3)).mean(axis=0)
        sc = [(np.diff(np.sign(P[:, -1, d, :].mean(axis=1))) != 0).sum() for d in range(3)]
        print(f"  <P_d> (top lev) = {np.round(Pm[-1],4)}; <|P̄_d|> = {np.round(Pabs[-1],4)}; sign changes over cfgs = {sc}")
        for sub, lab in ((False, "unsubtracted (center-symmetric)"), (True, "E1 subtracted")):
            f3 = lambda x: meff_cosh(corr(x, sub).mean(axis=-2))  # avg over 3 dirs: [lev, τ]
            f12 = lambda x: meff_cosh(corr(x[:, :, :2, :], sub).mean(axis=-2))
            fd = lambda x: meff_cosh(corr(x, sub))  # per dir
            m3, e3 = jackknife(P, nb, f3); m12, e12 = jackknife(P, nb, f12); md, ed = jackknife(P, nb, fd)
            print(f"  -- {lab}")
            for li, lev in enumerate(hdr["levels"]):
                print(f"   APE n={lev:>2} avg3: " + " ".join(fmt(m3[li, t], e3[li, t]) for t in range(9)))
            li = len(hdr["levels"]) - 1
            print(f"   APE n={hdr['levels'][li]} dirs1+2: " + " ".join(fmt(m12[li, t], e12[li, t]) for t in range(9)))
            for d in range(3):
                print(f"   APE n={hdr['levels'][li]} dir{d+1}: " + " ".join(fmt(md[li, d, t], ed[li, d, t]) for t in range(9)))
            results[("P", L, sub)] = dict(m3=m3, e3=e3, m12=m12, e12=e12, md=md, ed=ed, levels=hdr["levels"])
        li = len(hdr["levels"]) - 1
        for sub in (False, True):
            f3 = lambda x, sub=sub: meff_cosh(corr(x, sub).mean(axis=-2))
            f12 = lambda x, sub=sub: meff_cosh(corr(x[:, :, :2, :], sub).mean(axis=-2))
            for lo, hi in ((2, 5), (3, 8), (4, 10), (6, 12)):
                pm, pe = jackknife(P, nb, window_mean(f3, lo, hi)); qm, qe = jackknife(P, nb, window_mean(f12, lo, hi))
                print(f"  plateau {'sub ' if sub else 'unsub'} t∈[{lo},{hi}] APE n={hdr['levels'][li]}: avg3 {fmt(pm[li],pe[li])}  dirs1+2 {fmt(qm[li],qe[li])}")
        # amplitude / overlap at top level
        c = corr(P, False).mean(axis=-2)
        print(f"  C(0) per level (unsub, avg3) = {np.round(c[:,0],6)}; C(1)/C(0) = {np.round(c[:,1]/c[:,0],4)}")
        print()


if __name__ == "__main__":
    main()
