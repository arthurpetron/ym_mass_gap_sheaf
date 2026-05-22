"""Smoke test for Milestone 0.1.

Verifies that the test harness runs and the core scientific stack
(`numpy`, `scipy`, `sympy`, `matplotlib`) is importable in the dev
environment. This is the placeholder test required by Milestone 0.1;
it has no analytic content.
"""

from __future__ import annotations

import matplotlib
import numpy
import scipy
import sympy

import computations


def test_core_stack_importable() -> None:
    assert numpy.__version__
    assert scipy.__version__
    assert sympy.__version__
    assert matplotlib.__version__


def test_computations_package_importable() -> None:
    assert computations.__name__ == "computations"
