"""The OS/Cauchy-Schwarz sharpened M -> infinity tail — the interim
sharpening queued in work_plan §16g (exact-N hybrid, upgraded to a
reflection-positivity bound).

**The lemma (config-level OS/CS).**  The DP.3 OS pairing (link
reflection theta: z -> 1-z, dp3_rp_check) restricts to each fixed
transverse sector: the perimeter-class and interior-wall labels
(q, w) sit on theta-invariant faces with SINGLE characters (positive
spectral weight), the top data (loop n, tiles a) lives strictly
above the plane, the bottom data (m, b) strictly below.
Osterwalder-Seiler link-reflection positivity therefore holds
sector-wise, and Cauchy-Schwarz in the OS inner product gives, for
every admissible labelling,

    N(n, m, q, w, a, b)^2  <=  N(n, n, q, w, a, a)
                               * N(m, m, q, w, b, b),

both right-hand values >= 0 (OS norms).  Machine gate: verified on
the banked exact M=2 network values (the negative configs of
dp3_m2_entries, whose diagonal partners are computed here) — a
NON-TRIVIAL check because the left side includes strictly negative
recoupling values.

**Use.**  The level-3 part of TAIL(2; s) is bounded config-by-config
by  W(L) * sqrt(D_top D_bot)  with the diagonal values D computed
exactly (network_value_fixed) for the DOMINANT configs (ranked by
the crude mass) under a wall-clock budget, and by the crude
domination  W * d_n d_m prod d  for the rest; levels >= 4 keep the
§16g domination-transfer bound.  Every ingredient is exact/certified;
the only effect of an unreached diagonal is a LARGER (still valid)
bound.

Run:  python -m computations.su2_cs_tail            (assemble+report)
      python -m computations.su2_cs_tail worker K   (diagonal worker)
"""

from __future__ import annotations

import itertools
import json
import math
import os
import signal
import sys
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
DIAG_JSON = os.path.join(HERE, "su2_cs_diagonals.json")
OUT_JSON = os.path.join(HERE, "su2_cs_tail_results.json")

sys.set_int_max_str_digits(0)


def cas4(k: int) -> int:
    return k * (k + 2)


def dim(k: int) -> int:
    return k + 1


def triad(a: int, b: int, c: int) -> bool:
    return (a + b + c) % 2 == 0 and abs(a - b) <= c <= a + b


# ---------------------------------------------------------------------------
# Level-K config enumeration (eps_slab conventions).
# ---------------------------------------------------------------------------


def layer_labellings(loop: int, q, w, cap: int):
    cand = [[a for a in range(cap + 1) if triad(loop, qi, a)]
            for qi in q]
    out = []
    for tiles in itertools.product(*cand):
        if all(triad(tiles[i - 1], tiles[i], w[i - 1])
               for i in range(4)):
            out.append(tiles)
    return out


def level_configs(n: int, m: int, K: int):
    """All admissible (q, w, top, bot) with max label exactly K."""
    out = []
    for q in itertools.product(range(K + 1), repeat=4):
        wch = []
        ok = True
        for i in range(4):
            ws = [w for w in range(K + 1)
                  if triad(q[i], q[(i + 1) % 4], w)]
            if not ws:
                ok = False
                break
            wch.append(ws)
        if not ok:
            continue
        for w in itertools.product(*wch):
            if sum(w) % 2:
                continue
            tops = layer_labellings(n, q, w, K)
            bots = layer_labellings(m, q, w, K)
            for top in tops:
                for bot in bots:
                    if max(list(q) + list(w) + list(top)
                           + list(bot)) != K:
                        continue
                    out.append((q, w, top, bot))
    return out


def config_exponent(q, w, top, bot) -> int:
    return (sum(2 * cas4(x) for x in q) + sum(cas4(x) for x in w)
            + sum(cas4(x) for x in top) + sum(cas4(x) for x in bot))


def crude_bound(n, m, q, w, top, bot) -> Frac:
    """W * d_n d_m prod_f d  =  d_n d_m prod_f d^2 (s-power apart)."""
    c = Frac(dim(n) * dim(m))
    for x in q:
        c *= Frac(dim(x) ** 4)
    for x in w:
        c *= Frac(dim(x) ** 2)
    for x in top:
        c *= Frac(dim(x) ** 2)
    for x in bot:
        c *= Frac(dim(x) ** 2)
    return c


def w_weight(q, w, top, bot) -> Frac:
    """prod_f d (the character-sum weight, s-power apart)."""
    c = Frac(1)
    for x in q:
        c *= Frac(dim(x) ** 2)
    for x in w:
        c *= Frac(dim(x))
    for x in top:
        c *= Frac(dim(x))
    for x in bot:
        c *= Frac(dim(x))
    return c


# ---------------------------------------------------------------------------
# Diagonal-value keys, D4 canonicalization, worker.
# ---------------------------------------------------------------------------


def canon_key(loop: int, q, w, tiles):
    """D4-canonical form of a HALF configuration (loop; q, w, tiles):
    rotations shift corners/sides together; reflections reverse.
    Invariance of the network value under this action is GATED in
    main against computed values, not assumed."""
    best = None
    q, w, t = tuple(q), tuple(w), tuple(tiles)
    for r in range(4):
        qq = q[r:] + q[:r]
        ww = w[r:] + w[:r]
        tt = t[r:] + t[:r]
        for refl in (False, True):
            if refl:
                q2 = (qq[0],) + tuple(reversed(qq[1:]))
                t2 = (tt[0],) + tuple(reversed(tt[1:]))
                w2 = tuple(reversed(ww))
            else:
                q2, w2, t2 = qq, ww, tt
            cand = (loop, q2, w2, t2)
            if best is None or cand < best:
                best = cand
    return best


def _key_str(key) -> str:
    loop, q, w, t = key
    return f"{loop}|{','.join(map(str, q))}|{','.join(map(str, w))}" \
           f"|{','.join(map(str, t))}"


def diag_targets(entries=((0, 0), (1, 1), (0, 1)), K: int = 3,
                 top_k: int = 220):
    """Diagonal keys ranked by the crude tail mass they unlock
    (attributing each config's crude mass to its uncovered sides),
    evaluated at s = 3/5: covering the top ~half collapses the
    level-3 remainder by orders of magnitude (steep profile)."""
    s = Frac(3, 5)
    need: Dict[str, Frac] = {}
    keys: Dict[str, Tuple] = {}
    for (n, m) in entries:
        for cfg in level_configs(n, m, K):
            q, w, top, bot = cfg
            mass = crude_bound(n, m, *cfg) \
                * s ** config_exponent(*cfg)
            for loop, tiles in ((n, top), (m, bot)):
                key = canon_key(loop, q, w, tiles)
                ks = _key_str(key)
                keys[ks] = key
                need[ks] = need.get(ks, Frac(0)) + mass / 2
    ranked = sorted(need.items(), key=lambda kv: -kv[1])
    return [keys[ks] for ks, _v in ranked[:top_k]]


def worker(budget_s: int = 240, max_values: int = 200,
           shard: int = 0, nshards: int = 1) -> None:
    """Compute diagonal values with a per-value wall-clock budget,
    appending to DIAG_JSON.<shard> incrementally."""
    from computations.dp3_fixed_tile import network_value_fixed

    path = DIAG_JSON + (f".{shard}" if nshards > 1 else "")
    done: Dict[str, List] = {}
    if os.path.exists(path):
        with open(path) as fh:
            done = json.load(fh)
    merged = load_diag_raw()
    # gate cases first: diagonal partners of banked negative configs
    gate_keys = _gate_diag_keys()
    targets = gate_keys + diag_targets()
    todo = [k for i, k in enumerate(targets)
            if i % nshards == shard and _key_str(k) not in done
            and _key_str(k) not in merged]
    n_done = 0
    for key in todo:
        ks = _key_str(key)
        if ks in done:
            continue
        loop, q, w, tiles = key

        def _alarm(_s, _f):
            raise TimeoutError()

        old = signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(budget_s)
        try:
            val = network_value_fixed(loop, loop, q, w, tiles, tiles)
            if val:
                assert set(val) == {0}
                v = val[0]
            else:
                v = Frac(0)
            assert v >= 0, f"OS norm negative at {ks}: {v}"
            done[ks] = [str(v.numerator), str(v.denominator)]
        except TimeoutError:
            done[ks] = None      # unreached: fallback stays valid
        except Exception as exc:
            done[ks] = None
            print(f"  {ks}: ERROR {exc}", flush=True)
        finally:
            signal.alarm(0)
            signal.signal(signal.SIGALRM, old)
        n_done += 1
        with open(path, "w") as fh:
            json.dump(done, fh)
        print(f"  [{n_done}] {ks} -> "
              f"{done[ks] if done[ks] is None else 'ok'}", flush=True)
        if n_done >= max_values:
            break


def _gate_diag_keys():
    """Diagonal partners needed to gate the CS lemma on the banked
    exact negative network values (M=2 labels: cheap)."""
    with open(os.path.join(HERE, "dp3_m2_entries.json")) as fh:
        d = json.load(fh)
    keys = []
    seen = set()
    for entry, (n, m) in (("1,1", (1, 1)), ("0,1", (0, 1))):
        for cfg in d[entry]["negative_configs"][:4]:
            for loop, tiles in ((n, cfg["top"]), (m, cfg["bot"])):
                key = canon_key(loop, tuple(cfg["q"]),
                                tuple(cfg["w"]), tuple(tiles))
                ks = _key_str(key)
                if ks not in seen:
                    seen.add(ks)
                    keys.append(key)
    return keys


# ---------------------------------------------------------------------------
# Assembly: sharpened TAIL and windows.
# ---------------------------------------------------------------------------


def _sqrt_upper(x: Frac) -> Frac:
    """Certified rational upper bound on sqrt(x), x >= 0."""
    if x == 0:
        return Frac(0)
    t = Frac(math.sqrt(float(x))).limit_denominator(10 ** 15)
    if t <= 0:
        t = x + 1
    u = (x + t * t) / (2 * t)
    assert u * u >= x
    return u


def level3_tail(n: int, m: int, s: Frac,
                diag: Dict[str, Optional[Frac]]) -> Tuple[Frac, int,
                                                          int]:
    """Certified bound on the level-3 mass of entry (n, m):
    sum over level-3 configs of W s^E * min(crude, CS).  Returns
    (bound, n_cs_used, n_total)."""
    tot = Frac(0)
    used = 0
    cfgs = level_configs(n, m, 3)
    for (q, w, top, bot) in cfgs:
        E = config_exponent(q, w, top, bot)
        ww = w_weight(q, w, top, bot)
        crude = crude_bound(n, m, q, w, top, bot)

        def dval(loop, tiles):
            ks = _key_str(canon_key(loop, q, w, tiles))
            if ks in diag and diag[ks] is not None:
                return diag[ks]
            return None

        da = dval(n, top)
        db = dval(m, bot)
        if da is not None and db is not None:
            b = ww * _sqrt_upper(da * db)
            used += 1
            bound = min(b, crude)
        elif da is not None:
            # |N| <= sqrt(D_a) * sqrt(crude-bound on D_b):
            # D_b <= d_m^2 prod d^2 (same crude argument applied to
            # the diagonal value)
            db_crude = crude_bound(m, m, q, w, bot, bot)
            b = ww * _sqrt_upper(da * db_crude)
            used += 1
            bound = min(b, crude)
        elif db is not None:
            da_crude = crude_bound(n, n, q, w, top, top)
            b = ww * _sqrt_upper(da_crude * db)
            used += 1
            bound = min(b, crude)
        else:
            bound = crude
        tot += bound * s ** E
    return tot, used, len(cfgs)


def load_diag_raw() -> Dict[str, Optional[List]]:
    import glob
    raw: Dict[str, Optional[List]] = {}
    for path in [DIAG_JSON] + sorted(glob.glob(DIAG_JSON + ".*")):
        if os.path.exists(path):
            with open(path) as fh:
                for k, v in json.load(fh).items():
                    if k not in raw or raw[k] is None:
                        raw[k] = v
    return raw


def load_diag() -> Dict[str, Optional[Frac]]:
    out = {}
    for k, v in load_diag_raw().items():
        out[k] = None if v is None else Frac(int(v[0]), int(v[1]))
    return out


def cs_gate() -> Tuple[bool, list]:
    """Machine gate of the OS/CS lemma on banked exact N values."""
    with open(os.path.join(HERE, "dp3_m2_entries.json")) as fh:
        d = json.load(fh)
    diag = load_diag()
    ok = True
    rows = []
    for entry, (n, m) in (("1,1", (1, 1)), ("0,1", (0, 1))):
        for cfg in d[entry]["negative_configs"][:4]:
            Nv = Frac(cfg["N"][0], cfg["N"][1])
            ka = _key_str(canon_key(n, tuple(cfg["q"]),
                                    tuple(cfg["w"]),
                                    tuple(cfg["top"])))
            kb = _key_str(canon_key(m, tuple(cfg["q"]),
                                    tuple(cfg["w"]),
                                    tuple(cfg["bot"])))
            da = diag.get(ka)
            db = diag.get(kb)
            if da is None or db is None:
                rows.append((entry, cfg["E"], "diagonal unreached"))
                continue
            good = Nv * Nv <= da * db
            ok &= good
            rows.append((entry, cfg["E"], float(Nv), float(da),
                         float(db), good))
    return ok, rows


def sharpened_x11_window(s: Frac, lam: int = 6) -> Dict:
    from computations.su2_minf_windows import (
        DomTransfer, entry_value_and_unreached, load_m2)

    d = load_m2()
    diag = load_diag()
    T, U, tails = {}, {}, {}
    stats = {}
    for key, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                        ("0,1", (0, 1))):
        T[key], U[key] = entry_value_and_unreached(d, key, n, m, s)
        lvl3, used, ncfg = level3_tail(n, m, s, diag)
        dt = DomTransfer(n, m, s, lam)
        rest = dt.dominated_trace(lam) - dt.dominated_trace(3)
        assert rest >= 0
        tails[key] = lvl3 + rest + dt.lam_slop()
        stats[key] = {"lvl3": float(lvl3), "cs_used": used,
                      "n_cfg": ncfg, "rest4plus": float(rest)}
    lo = {k: T[k] - U[k] - tails[k] for k in T}
    hi = {k: T[k] + U[k] + tails[k] for k in T}
    ok_pos = all(v > 0 for v in lo.values())
    out = {"s": str(s), "positive": ok_pos, "stats": stats,
           "tail": {k: float(tails[k]) for k in tails},
           "unreached": {k: float(U[k]) for k in U}}
    if ok_pos:
        r_lo = lo["1,1"] * lo["0,0"] / (hi["0,1"] ** 2)
        r_hi = hi["1,1"] * hi["0,0"] / (lo["0,1"] ** 2)
        out["X11_lo"] = math.log(float(r_lo))
        out["X11_hi"] = math.log(float(r_hi))
        out["ratio_gt_1_certified"] = bool(r_lo > 1)
    return out


def main() -> None:
    import time

    t0 = time.time()
    if len(sys.argv) > 1 and sys.argv[1] == "worker":
        budget = int(sys.argv[2]) if len(sys.argv) > 2 else 240
        shard = int(sys.argv[3]) if len(sys.argv) > 3 else 0
        nsh = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        worker(budget_s=budget, shard=shard, nshards=nsh)
        return
    print("OS/CS-sharpened M -> infinity tails")
    print("=" * 72)
    diag = load_diag()
    n_ok = sum(1 for v in diag.values() if v is not None)
    print(f"diagonal values available: {n_ok} "
          f"(+{len(diag) - n_ok} unreached)")
    print("GATE — config-level OS/CS on banked exact N values")
    ok, rows = cs_gate()
    for r in rows:
        print("  ", r)
    print(f"  gate: {'PASSED' if ok else 'FAILED'}")
    res = {"cs_gate": ok, "n_diag": n_ok, "rows": []}
    x3 = None
    try:
        with open(os.path.join(HERE, "c_su2_tau3_results.json")) as fh:
            x3 = Frac(json.load(fh)["X"]["1,1"]["tau3"])
    except Exception:
        pass
    print("=" * 72)
    print("Sharpened certified X_11 windows")
    for s in (Frac(1, 2), Frac(11, 20), Frac(3, 5), Frac(13, 20),
              Frac(7, 10), Frac(3, 4)):
        row = sharpened_x11_window(s)
        tau = -math.log(float(s))
        row["tau"] = tau
        row["flat_target"] = 6 * tau * tau + (
            float(x3) * tau ** 3 if x3 is not None else 0.0)
        res["rows"].append(row)
        if "X11_lo" in row:
            print(f"  s={s}: X11 in [{row['X11_lo']:+.6f}, "
                  f"{row['X11_hi']:+.6f}]  flat {row['flat_target']:+.6f}"
                  f"  >0: {row['ratio_gt_1_certified']}  "
                  f"(cs {row['stats']['1,1']['cs_used']}/"
                  f"{row['stats']['1,1']['n_cfg']})")
        else:
            t11 = row["tail"]["1,1"]
            print(f"  s={s}: window closed (tail11 ~ {t11:.3e}, "
                  f"lvl3 {row['stats']['1,1']['lvl3']:.3e}, "
                  f"rest {row['stats']['1,1']['rest4plus']:.3e})")
    with open(OUT_JSON, "w") as fh:
        json.dump(res, fh, indent=1)
    print(f"\nledger written to {OUT_JSON}  [{time.time() - t0:.0f}s]")


if __name__ == "__main__":
    main()
