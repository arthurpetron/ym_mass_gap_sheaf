"""M=2 finality repair: direct evaluation of the banked UNREACHED
configs (work_plan §16h queue — the U_2 side of the window).

The dp3_m2_entries ledger lists, per entry, the configs whose Haar
value never landed under the original 300 s budget (labels all
<= 2).  Each value computed here moves its config from the U_2
uncertainty into the exact T_2 value: the window tightens on BOTH
sides.  Values are stored in a separate ledger
(`su2_m2_finality.json`) keyed by entry and config — the banked
dp3_m2_entries file is never modified.

Run:  python -m computations.su2_m2_finality worker [budget] [shard] [nshards]
      python -m computations.su2_m2_finality           (status)
"""

from __future__ import annotations

import json
import os
import signal
import sys
import time
from fractions import Fraction
from typing import Dict, Optional

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "su2_m2_finality.json")

sys.set_int_max_str_digits(0)


def _cfg_key(entry: str, cfg: dict) -> str:
    return (f"{entry}|{','.join(map(str, cfg['q']))}"
            f"|{','.join(map(str, cfg['w']))}"
            f"|{','.join(map(str, cfg['top']))}"
            f"|{','.join(map(str, cfg['bot']))}")


def targets():
    with open(os.path.join(HERE, "dp3_m2_entries.json")) as fh:
        d = json.load(fh)
    out = []
    for entry in ("0,0", "1,1", "0,1"):
        for cfg in d[entry]["unreached"]:
            if "q" not in cfg:
                continue
            out.append((entry, cfg))
    # cheap-looking first: rank by label sum (proxy for cost) then E
    out.sort(key=lambda ec: (sum(ec[1]["q"]) + sum(ec[1]["w"])
                             + sum(ec[1]["top"]) + sum(ec[1]["bot"]),
                             ec[1]["E"]))
    return out


def _load(path):
    if os.path.exists(path):
        with open(path) as fh:
            return json.load(fh)
    return {}


def load_all() -> Dict[str, Optional[list]]:
    import glob
    raw: Dict[str, Optional[list]] = {}
    for path in [OUT_JSON] + sorted(glob.glob(OUT_JSON + ".*")):
        for k, v in _load(path).items():
            if k not in raw or raw[k] is None:
                raw[k] = v
    return raw


def worker(budget_s: int = 600, shard: int = 0,
           nshards: int = 1) -> None:
    from computations.su2_cut_eval import network_value_fast

    path = OUT_JSON + (f".{shard}" if nshards > 1 else "")
    done = _load(path)
    merged = load_all()
    ent_nm = {"0,0": (0, 0), "1,1": (1, 1), "0,1": (0, 1)}
    todo = [(e, c) for i, (e, c) in enumerate(targets())
            if i % nshards == shard]
    for (entry, cfg) in todo:
        ks = _cfg_key(entry, cfg)
        if ks in done or ks in merged:
            continue
        n, m = ent_nm[entry]
        t0 = time.time()
        v = network_value_fast(
            n, m, tuple(cfg["q"]), tuple(cfg["w"]),
            tuple(cfg["top"]), tuple(cfg["bot"]),
            per_order_s=0 or 1, greedy_first_s=budget_s,
            orders=[])
        if v is None:
            done[ks] = None
        else:
            done[ks] = [str(v.numerator), str(v.denominator)]
        with open(path, "w") as fh:
            json.dump(done, fh)
        print(f"  {ks} -> "
              f"{'ok ' + str(float(v)) if v is not None else 'TIMEOUT'}"
              f" [{time.time() - t0:.0f}s]", flush=True)


def resolved_and_residual(entry: str, n: int, m: int, s: Frac):
    """(exact addition to T_2, remaining U_2 bound) for `entry` at
    coupling s, consuming every landed direct value; the rest keeps
    the crude per-config bound (CS-diagonal sharpening of the
    remainder is folded in by the window assembly if partners are
    available in the CS ledger)."""
    with open(os.path.join(HERE, "dp3_m2_entries.json")) as fh:
        d = json.load(fh)
    vals = load_all()
    add = Frac(0)
    residual = Frac(0)
    n_res = 0
    for cfg in d[entry]["unreached"]:
        if "q" not in cfg:
            continue
        ks = _cfg_key(entry, cfg)
        E = cfg["E"]
        # W = prod_f d s^C  (loop dims excluded)
        Wd = Frac(1)
        for x in cfg["q"]:
            Wd *= Frac((x + 1) ** 2)
        for x in cfg["w"]:
            Wd *= Frac(x + 1)
        for x in cfg["top"]:
            Wd *= Frac(x + 1)
        for x in cfg["bot"]:
            Wd *= Frac(x + 1)
        if ks in vals and vals[ks] is not None:
            v = Frac(int(vals[ks][0]), int(vals[ks][1]))
            add += Wd * v * s ** E
            n_res += 1
        else:
            crude = Wd * Frac((n + 1) * (m + 1))
            for x in (list(cfg["q"]) + list(cfg["w"])
                      + list(cfg["top"]) + list(cfg["bot"])):
                crude *= Frac(x + 1)
            for x in cfg["q"]:
                crude *= Frac(x + 1)   # second face of the class
            residual += crude * s ** E
    return add, residual, n_res


def main() -> None:
    if len(sys.argv) > 1 and sys.argv[1] == "worker":
        b = int(sys.argv[2]) if len(sys.argv) > 2 else 600
        sh = int(sys.argv[3]) if len(sys.argv) > 3 else 0
        ns = int(sys.argv[4]) if len(sys.argv) > 4 else 1
        worker(b, sh, ns)
        return
    vals = load_all()
    ok = sum(1 for v in vals.values() if v is not None)
    print(f"M=2 finality: {ok} direct values landed, "
          f"{sum(1 for v in vals.values() if v is None)} timeouts, "
          f"{len(targets())} targets total")
    for entry, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                          ("0,1", (0, 1))):
        add, res, k = resolved_and_residual(entry, n, m, Frac(3, 5))
        print(f"  {entry}: resolved {k} configs; T2 += "
              f"{float(add):.3e}; residual U2 bound {float(res):.3e}"
              f" (s = 3/5)")


if __name__ == "__main__":
    main()


# ---------------------------------------------------------------------------
# Combined window: direct values + CS-sharpened U_2 + sharpened tails.
# ---------------------------------------------------------------------------


def cs_sharpened_u2(entry: str, n: int, m: int, s: Frac):
    """U_2 residual with per-config OS/CS bounds where diagonal
    partners are available: min(crude, W sqrt(D_a D_b))."""
    from computations.su2_cs_tail import (canon_key, _key_str,
                                          load_diag, _sqrt_upper)
    with open(os.path.join(HERE, "dp3_m2_entries.json")) as fh:
        d = json.load(fh)
    vals = load_all()
    diag = load_diag()
    add = Frac(0)
    residual = Frac(0)
    n_res = n_cs = 0
    for cfg in d[entry]["unreached"]:
        if "q" not in cfg:
            continue
        ks = _cfg_key(entry, cfg)
        E = cfg["E"]
        Wd = Frac(1)
        for x in cfg["q"]:
            Wd *= Frac((x + 1) ** 2)
        for x in cfg["w"]:
            Wd *= Frac(x + 1)
        for x in cfg["top"]:
            Wd *= Frac(x + 1)
        for x in cfg["bot"]:
            Wd *= Frac(x + 1)
        if ks in vals and vals[ks] is not None:
            v = Frac(int(vals[ks][0]), int(vals[ks][1]))
            add += Wd * v * s ** E
            n_res += 1
            continue
        crude = Wd * Frac((n + 1) * (m + 1))
        for x in (list(cfg["q"]) + list(cfg["w"])
                  + list(cfg["top"]) + list(cfg["bot"])):
            crude *= Frac(x + 1)
        for x in cfg["q"]:
            crude *= Frac(x + 1)
        ka = _key_str(canon_key(n, tuple(cfg["q"]), tuple(cfg["w"]),
                                tuple(cfg["top"])))
        kb = _key_str(canon_key(m, tuple(cfg["q"]), tuple(cfg["w"]),
                                tuple(cfg["bot"])))
        da, db = diag.get(ka), diag.get(kb)
        if da is not None and db is not None:
            b = Wd * _sqrt_upper(da * db)
            n_cs += 1
            bound = min(b, crude)
        else:
            bound = crude
        residual += bound * s ** E
    return add, residual, n_res, n_cs


def combined_x11_window(s: Frac, lam: int = 8):
    """The full assembly: T_2 + direct finality values, CS-sharpened
    U_2, CS-sharpened level-3 tail, domination levels >= 4.

    lam = 8 default (work_plan section 16k): the Lambda-cap union
    bound `lam_slop` falls from ~4e-5 to ~3e-12 at s = 5/8 between
    lam = 6 and lam = 8 while the dominated rest is unchanged — the
    slop at lam = 6 was pure union-bound slack, and removing it
    marched the positive-window boundary from s = 3/5 past
    s = 8/13."""
    import math as _math
    from computations.su2_minf_windows import (
        DomTransfer, entry_value_and_unreached, load_m2)
    from computations.su2_cs_tail import level3_tail, load_diag

    d = load_m2()
    diag = load_diag()
    T, U, tails, stats = {}, {}, {}, {}
    for key, (n, m) in (("0,0", (0, 0)), ("1,1", (1, 1)),
                        ("0,1", (0, 1))):
        t2, _u_old = entry_value_and_unreached(d, key, n, m, s)
        add, resid, n_res, n_cs = cs_sharpened_u2(key, n, m, s)
        T[key] = t2 + add
        U[key] = resid
        lvl3, used, ncfg = level3_tail(n, m, s, diag)
        dt = DomTransfer(n, m, s, lam)
        rest = dt.dominated_trace(lam) - dt.dominated_trace(3)
        assert rest >= 0
        tails[key] = lvl3 + rest + dt.lam_slop()
        stats[key] = {"u2_resolved": n_res, "u2_cs": n_cs,
                      "u2_residual": float(resid),
                      "lvl3": float(lvl3), "cs_used": used}
    lo = {k: T[k] - U[k] - tails[k] for k in T}
    hi = {k: T[k] + U[k] + tails[k] for k in T}
    out = {"s": str(s), "stats": stats,
           "tail": {k: float(tails[k]) for k in tails},
           "positive": all(v > 0 for v in lo.values())}
    if out["positive"]:
        r_lo = lo["1,1"] * lo["0,0"] / (hi["0,1"] ** 2)
        r_hi = hi["1,1"] * hi["0,0"] / (lo["0,1"] ** 2)
        out["X11_lo"] = _math.log(float(r_lo))
        out["X11_hi"] = _math.log(float(r_hi))
        out["ratio_gt_1_certified"] = bool(r_lo > 1)
    return out
