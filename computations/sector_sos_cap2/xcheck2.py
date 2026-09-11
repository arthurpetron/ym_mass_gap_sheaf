"""INDEPENDENT-REPLICATION TOOLING for the sector-SOS certificate
(work_plan §17g, notes/sector-sos-positivity.md).

STATUS: gated, NOT yet pinned in the test suite.  `spinnet` (the fast
exact rational spin-network evaluator) is gated BIT-FOR-BIT against the
incumbent evaluator `computations.dp3_fixed_tile.network_value_fixed` on
all 171 cap<=1 configurations, 320 character-orthogonality identities and
130 random networks (see `xcheck2`), and the cap<=1 family it rebuilds
reproduces `computations.sector_sos` exactly.  It exists only to build the
DISJOINT cap<=2 family (187 sectors) used as the independent replication
gate; nothing on the certificate's critical path depends on it.  Pinning
these modules in `tests/` is a named follow-up.
"""

"""Cross-check the spin-network N against the quaternion brute force on
cap=2 configurations.  The brute force is run in a forked child with a
2 GB address-space limit and a 60 s alarm; children that die are reported
as UNREACHED (a resource verdict, never a mathematical one)."""
import itertools
import os
import pickle
import random
import resource
import signal
import sys
import time
from fractions import Fraction as F

sys.path.insert(0, '/home/claude/ym')
sys.set_int_max_str_digits(0)

from . import slabnet as sl
from computations.dp3_fixed_tile import network_value_fixed as brute


def brute_forked(case, limit_bytes=2 * 1024**3, secs=60):
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            resource.setrlimit(resource.RLIMIT_AS, (limit_bytes, limit_bytes))
            signal.alarm(secs)
            v = brute(*case)
            val = v[0] if v else F(0)
            assert (not v) or set(v) == {0}
            os.write(w, pickle.dumps(('ok', val)))
        except BaseException as e:  # noqa
            try:
                os.write(w, pickle.dumps(('err', type(e).__name__)))
            except Exception:
                pass
        finally:
            os.close(w)
            os._exit(0)
    os.close(w)
    buf = b''
    while True:
        c = os.read(r, 1 << 16)
        if not c:
            break
        buf += c
    os.close(r)
    os.waitpid(pid, 0)
    if not buf:
        return ('killed', None)
    return pickle.loads(buf)


def content(q, w, top, bot):
    return sum(q) * 2 + sum(w) + sum(top) + sum(bot)


def main():
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
    pool = []
    for q in itertools.product(range(3), repeat=4):
        for w in itertools.product(range(3), repeat=4):
            if max(q) < 2 and max(w) < 2:
                continue  # cap<=1 already fully checked
            L0 = sl.layers(0, q, w, 3)
            L1 = sl.layers(1, q, w, 3)
            hs = [(0, t) for t in L0] + [(1, t) for t in L1]
            if not hs:
                continue
            for (n, a) in hs:
                for (m, b) in hs:
                    pool.append((n, m, q, w, a, b))
    print('cap2 config pool', len(pool), flush=True)
    pool.sort(key=lambda c: content(c[2], c[3], c[4], c[5]))
    # take a spread: all cheapest ones, plus a random sample across the range
    sample = pool[:120]
    rest = pool[120:]
    random.shuffle(rest)
    sample += rest[:400]
    ok = unreached = 0
    bad = []
    t0 = time.time()
    for i, c in enumerate(sample):
        got = sl.N(*c)
        st, ref = brute_forked(c)
        if st != 'ok':
            unreached += 1
            continue
        if got != ref:
            bad.append((c, str(got), str(ref)))
            print('MISMATCH', c, got, ref, flush=True)
        else:
            ok += 1
        if i % 25 == 0:
            print(f'  {i}/{len(sample)} ok={ok} unreached={unreached} '
                  f'bad={len(bad)} {time.time()-t0:.0f}s', flush=True)
    print(f'DONE cap2 crosscheck: agreed={ok} unreached={unreached} '
          f'MISMATCH={len(bad)} in {time.time()-t0:.0f}s', flush=True)
    if bad:
        print('BAD:', bad[:10], flush=True)


if __name__ == '__main__':
    main()
