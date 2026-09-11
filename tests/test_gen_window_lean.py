"""Pins for the WindowLedger.lean generator (work_plan §16l).

Pure Python; never invokes Lean (host safety).  The Lean-side
verification protocol (pinned-toolchain elaboration, axiom audit,
mutation battery) is recorded in dual_kappa_spike/README.md.
"""

import os
import subprocess
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
GEN = os.path.join(ROOT, "scripts", "gen_window_lean.py")


@pytest.fixture(scope="module")
def emitted() -> str:
    proc = subprocess.run([sys.executable, GEN], capture_output=True,
                          timeout=1800)
    assert proc.returncode == 0, proc.stderr.decode()[:2000]
    return proc.stdout.decode()


def test_emits_all_theorems(emitted):
    for thm in ("cited_nonneg", "cs_valid00", "cs_valid11",
                "cs_valid01", "grid_tails_nonneg",
                "windows_positive", "x11_ratio_certified"):
        assert f"theorem {thm}" in emitted, thm
    for bad in ("Classical", "native_decide", "sorry", "axiom "):
        assert bad not in emitted, bad


def test_grid_contents(emitted):
    """The CERT grid must contain the banked §16k boundary points and
    the positivity grid the two open-ratio points."""
    assert "certGrid.length = 7" in emitted
    assert "posGrid.length = 2" in emitted
    # the CERT boundary and the s=1/2 anchor appear as grid rows
    assert "(8, 13, (" in emitted
    assert "(1, 2, (" in emitted
    # the positivity-only rows
    assert "(31, 50, (" in emitted
    assert "(5, 8, (" in emitted


def test_generator_asserts_are_live(emitted):
    """The soundness pre-checks inside the generator (positivity and
    ratio at every grid point, T cross-check against the reference
    assembly, r^2 >= Da*Db) are executed on every run — the emitted
    file exists only if they all passed.  Spot-check one: the 8/13
    X11 lower bound recorded in the docstring is positive."""
    line = [ln for ln in emitted.splitlines()
            if ln.strip().startswith("s = 8/13: X_11 >=")]
    assert len(line) == 1
    val = float(line[0].split(">=")[1])
    assert val > 0
