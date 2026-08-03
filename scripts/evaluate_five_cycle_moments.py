#!/usr/bin/env python3
"""Evaluate the cutoff-one Haar-five balance and print the progress chart."""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from computations.cutoff_one_haar5_moment_balance import (  # noqa: E402
    cutoff_one_haar5_moment_balance,
    render_balance_report,
)
from computations.cutoff_one_surface_haar_orbits import (  # noqa: E402
    cutoff_one_surface_haar_orbit_audit,
    render_surface_haar_orbit_audit,
)
from scripts.five_cycle_progress import (  # noqa: E402
    DEFAULT_STATE_PATH,
    apply_overrides,
    load_state,
    render_chart,
)


def main() -> int:
    balance = cutoff_one_haar5_moment_balance()
    if not balance.validates():
        raise AssertionError("the exact cutoff-one Haar-five certificate failed")
    orbit_audit = cutoff_one_surface_haar_orbit_audit()
    if not orbit_audit.validates():
        raise AssertionError("the exact cutoff-one surface-orbit audit failed")

    state = load_state(DEFAULT_STATE_PATH)
    apply_overrides(
        state,
        [
            "haar5_evaluation=complete",
            "haar5_comparison=complete",
            "centered_balance=complete",
        ],
    )
    evidence = state.setdefault("evidence", {})
    evidence["haar5_cycle_space"] = f"{balance.closed_surface_count}/128"
    evidence["slab_embedding"] = "128/128-closed-complete"
    evidence["centered_defect"] = "strictly-positive-for-w>0"
    evidence["surface_orbit_haar"] = (
        f"{orbit_audit.validated_orbit_count}/"
        f"{len(orbit_audit.records)}-exact-representatives-cover-"
        f"{orbit_audit.covered_surface_count}/128"
    )
    DEFAULT_STATE_PATH.write_text(
        json.dumps(state, indent=2) + "\n",
        encoding="utf-8",
    )

    print(render_balance_report(balance))
    print()
    print(render_surface_haar_orbit_audit(orbit_audit))
    print()
    print(render_chart(state))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
