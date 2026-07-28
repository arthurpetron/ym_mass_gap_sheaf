"""One-configuration worker for the M=2 fixed-tile kernel.

Runs as a subprocess so that a contraction which exhausts memory or
wall-clock kills only this child.  The parent records that configuration
as UNREACHED and restarts a fresh worker; the run continues.

Protocol: one JSON request per stdin line, one JSON reply per stdout
line.  Request {"n","m","q","w","top","bot"}; reply {"N":[num,den]}.
"""
from __future__ import annotations

import json
import resource
import sys

sys.path.insert(0, "/home/claude/dp3m2")

import os

LIMIT = int(float(os.environ.get("WORKER_GB", "1.8")) * 1024 ** 3)
resource.setrlimit(resource.RLIMIT_AS, (LIMIT, LIMIT))

from computations.dp3_fixed_tile import network_value_fixed  # noqa: E402


def main():
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        v = network_value_fixed(r["n"], r["m"], tuple(r["q"]),
                                tuple(r["w"]), tuple(r["top"]),
                                tuple(r["bot"]))
        N = v[0] if v else 0
        num = N.numerator if hasattr(N, "numerator") else int(N)
        den = N.denominator if hasattr(N, "denominator") else 1
        sys.stdout.write(json.dumps({"N": [num, den]}) + "\n")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
