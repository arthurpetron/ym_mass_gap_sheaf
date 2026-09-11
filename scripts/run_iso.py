"""Process-isolated driver for the M=2 fixed-tile kernel.

Each configuration is evaluated in a subprocess worker.  A worker that
exceeds its wall-clock budget or its 1.8 GB address-space limit is killed
and replaced; the configuration is recorded as UNREACHED and the run
continues.  Two earlier runs died instead — one OOM-killed outright, one
in a cascade of MemoryErrors raised inside its own exception handler
(at that point even `import gc` could not allocate).  Isolation, not a
bigger try/except, is the fix.

Configurations are visited in ascending exponent E, so every assembled
coefficient below the smallest UNREACHED E is FINAL.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time
from fractions import Fraction

sys.path.insert(0, "/home/claude/dp3m2")

from computations.dp3_fixed_tile import layer_labellings      # noqa: E402
from computations.dp3_m2_driver import _classes, wpow         # noqa: E402
from computations.exact_haar_network import casimir4, dim     # noqa: E402

Frac = Fraction
M = 2
PAIRS = [tuple(int(x) for x in p.split(",")) for p in sys.argv[1].split(";")]
TAG = sys.argv[2]
BUDGET = int(sys.argv[3]) if len(sys.argv) > 3 else 200
CACHE = f"/home/claude/dp3m2/fx_cache_{TAG}.json"
OUT = f"/home/claude/dp3m2/fx_{TAG}.json"
SHARED = ["/home/claude/dp3m2/fx_cache_P.json",
          "/home/claude/dp3m2/fx_cache_Q.json",
          "/home/claude/dp3m2/fx_cache_R.json",
          "/home/claude/dp3m2/fx_cache_S2.json"]


def load_cache():
    c = {}
    for path in SHARED + [CACHE]:
        if not os.path.exists(path):
            continue
        for k, v in json.load(open(path)).items():
            if k in c and c[k] is not None:
                continue
            c[k] = None if v is None else Frac(v[0], v[1])
    return c


def save_cache(c):
    tmp = CACHE + ".tmp"
    json.dump({k: (None if v is None else [v.numerator, v.denominator])
               for k, v in c.items()}, open(tmp, "w"))
    os.replace(tmp, CACHE)


class Worker:
    def __init__(self):
        self.p = None
        self.start()

    def start(self):
        self.p = subprocess.Popen(
            [sys.executable, "-u", "/home/claude/dp3m2/worker_fixed.py"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True)

    def kill(self):
        try:
            self.p.kill()
            self.p.wait(timeout=10)
        except Exception:
            pass

    def ask(self, req, budget):
        """Return Fraction, or None if the worker failed/timed out."""
        try:
            self.p.stdin.write(json.dumps(req) + "\n")
            self.p.stdin.flush()
        except Exception:
            self.kill()
            self.start()
            return None
        deadline = time.time() + budget
        os.set_blocking(self.p.stdout.fileno(), False)
        buf = ""
        while time.time() < deadline:
            if self.p.poll() is not None:      # worker died (OOM)
                break
            try:
                chunk = self.p.stdout.read()
            except Exception:
                chunk = None
            if chunk:
                buf += chunk
                if "\n" in buf:
                    os.set_blocking(self.p.stdout.fileno(), True)
                    try:
                        return Frac(*json.loads(buf.split("\n")[0])["N"])
                    except Exception:
                        break
            else:
                time.sleep(0.05)
        self.kill()
        self.start()
        return None


def configs(n, m):
    out = []
    for rep, members in _classes(M).items():
        q, w = rep
        tops = layer_labellings(n, q, w, M)
        bots = layer_labellings(m, q, w, M)
        if not tops or not bots:
            continue
        base = wpow(q, w)
        for top in tops:
            for bot in bots:
                E = (base + sum(casimir4(a) for a in top)
                     + sum(casimir4(b) for b in bot))
                out.append((E, q, w, top, bot, len(members)))
    out.sort(key=lambda r: (r[0], r[1], r[2], r[3], r[4]))
    return out


def main():
    cache = load_cache()
    results = json.load(open(OUT)) if os.path.exists(OUT) else {}
    wk = Worker()
    for (n, m) in PAIRS:
        key = f"{n},{m}"
        if key in results:
            print(f"[{TAG}] T[{n},{m}] cached", flush=True)
            continue
        cfgs = configs(n, m)
        print(f"[{TAG}] T[{n},{m}]: {len(cfgs)} configurations", flush=True)
        poly, census, unreached = {}, [], []
        t0, dirty = time.time(), 0
        for E, q, w, top, bot, mult in cfgs:
            ck = f"{n}|{m}|{q}|{w}|{top}|{bot}"
            if ck in cache:
                N = cache[ck]
            else:
                ts = time.time()
                N = wk.ask({"n": n, "m": m, "q": list(q), "w": list(w),
                            "top": list(top), "bot": list(bot)}, BUDGET)
                dt = time.time() - ts
                cache[ck] = N
                dirty += 1
                if N is None:
                    print(f"    UNREACHED E={E} q={q} w={w} top={top} "
                          f"bot={bot} ({dt:.0f}s)", flush=True)
                elif dt > 20:
                    print(f"    E={E} q={q} w={w}: {dt:.0f}s N={N}",
                          flush=True)
                if dirty >= 3:
                    save_cache(cache)
                    dirty = 0
            if N is None:
                unreached.append({"E": E, "q": list(q), "w": list(w),
                                  "top": list(top), "bot": list(bot)})
                continue
            census.append({"E": E, "N": [N.numerator, N.denominator],
                           "q": list(q), "w": list(w),
                           "top": list(top), "bot": list(bot)})
            if not N:
                continue
            c = N * mult
            for qi in q:
                c *= dim(qi) ** 2
            for wi in w:
                c *= dim(wi)
            for a in top:
                c *= dim(a)
            for b in bot:
                c *= dim(b)
            poly[E] = poly.get(E, Frac(0)) + c
        save_cache(cache)
        poly = {k: v for k, v in poly.items() if v}
        D = min((u["E"] for u in unreached), default=None)
        neg_cfg = [r for r in census if Frac(*r["N"]) < 0]
        results[key] = {
            "poly": {str(p): [c.numerator, c.denominator]
                     for p, c in sorted(poly.items())},
            "n_terms": len(poly),
            "n_configs": len(census),
            "n_unreached": len(unreached),
            "exact_below_E": D,
            "n_negative_configs": len(neg_cfg),
            "negative_configs": neg_cfg,
            "negative_coeffs": {str(p): [c.numerator, c.denominator]
                                for p, c in sorted(poly.items()) if c < 0},
            "unreached": unreached,
            "seconds": round(time.time() - t0, 1),
        }
        json.dump(results, open(OUT, "w"), indent=1)
        print(f"[{TAG}] T[{n},{m}]: {len(poly)} terms, {len(census)} configs, "
              f"{len(neg_cfg)} with N<0, {len(unreached)} unreached, "
              f"FINAL below E={D}, {results[key]['seconds']}s", flush=True)
    wk.kill()
    print(f"[{TAG}] DONE", flush=True)


if __name__ == "__main__":
    main()
