"""DP.2 background driver: full kernel at truncation M, cutoff N."""
import json
import sys
import time

sys.path.insert(0, "/home/claude/ym_dig")

from computations.slab_blocking_kernel import kernel_entry_skeleton, skeleton_value

N = int(sys.argv[1]) if len(sys.argv) > 1 else 2
M = int(sys.argv[2]) if len(sys.argv) > 2 else 2
OUT = sys.argv[3] if len(sys.argv) > 3 else f"/home/claude/ym_dig/scratch/dp2_kernel_N{N}_M{M}.json"

a = skeleton_value(1, 0, (1, 0, 1, 0), (1, 1, 1, 1), min(M, 2))
b = skeleton_value(1, 0, (0, 1, 0, 1), (1, 1, 1, 1), min(M, 2))
print("nonzero-skeleton rotation gate:", a == b, flush=True)
assert a == b and a

T, UNREACHED = {}, {}
for n in range(N + 1):
    for m in range(n, N + 1):
        t0 = time.time()
        e = kernel_entry_skeleton(n, m, M, progress=True)
        un = kernel_entry_skeleton.last_unreached
        T[f"{n},{m}"] = {str(p): [c.numerator, c.denominator] for p, c in e.items()}
        if un:
            UNREACHED[f"{n},{m}"] = [str(u) for u in un]
        print(f"T[{n},{m}] done: {len(e)} terms, {len(un)} UNREACHED classes, "
              f"{time.time()-t0:.1f}s", flush=True)
        with open(OUT, "w") as fh:
            json.dump({"N": N, "M": M, "T": T, "unreached": UNREACHED}, fh)
print("ALL DONE", flush=True)
