"""Pins for DP.6 signed-sector survival over the full triple corpus.

One module-scoped sweep of all C(128,3) = 341,376 triples (~15 s)
backs every pin; the pinned literals are the ones banked in
lean_out/DP6Ledger.lean (via lean_out/gen_dp6_lean.py).
"""

from fractions import Fraction

import pytest

from computations.dp6_signed_survival import (
    lower_sector_poly,
    sweep_triples,
)

# The four negative-channel classes (per-class survival FAILS here;
# each channel is a single monomial, so its sign is s-independent).
NEG_CLASS_SUMS = {
    ((1, 8), (2, 11), (3, 4)): Fraction(-1, 60466176),
    ((1, 9), (2, 12), (3, 1)): Fraction(-7, 12754584),
    ((1, 10), (2, 11), (3, 2)): Fraction(-11, 76527504),
    ((1, 11), (2, 11), (3, 1)): Fraction(-5, 38263752),
}

# Exact value of the triples-only global sum at s = 1/2
# (dp6_results.json global.endpoints["1/2"]).
GLOBAL_TRIPLES_AT_HALF = Fraction(
    "65971246237970371262640113026433822080492256524337724401/"
    "33321467285754422353638125946786347725900401279079992232809332736"
)


@pytest.fixture(scope="module")
def sweep():
    """One full triple sweep shared by every test in this module."""
    (classes, n_eval, n_negative, min_z, min_z_profile,
     neg_all_spin3) = sweep_triples(progress_every=0)
    return {
        "classes": classes,
        "n_eval": n_eval,
        "n_negative": n_negative,
        "min_z": min_z,
        "min_z_profile": min_z_profile,
        "neg_all_spin3": neg_all_spin3,
    }


def _global_poly(classes):
    acc = {}
    for rec in classes.values():
        for k, v in rec.poly.items():
            acc[k] = acc.get(k, Fraction(0)) + v
    return {k: v for k, v in acc.items() if v}


def test_sanity_pins_15a(sweep):
    """Corpus census (§15a): 341,376 triples, 32,384 negative, every
    negative has a spin-3 face, minimal exemplar Z = -1/3981312 at
    spin profile {1: x9, 2: x6, 3: x3}."""
    assert sweep["n_eval"] == 341_376
    assert sweep["n_negative"] == 32_384
    assert sweep["neg_all_spin3"]
    assert sweep["min_z"] == Fraction(-1, 3981312)
    assert sweep["min_z_profile"] == ((1, 9), (2, 6), (3, 3))


def test_negative_class_sums_exactly(sweep):
    """Per-class survival fails at exactly four classes, with exactly
    these channel sums (the Lakatos fence banked by DP6Ledger.lean)."""
    got = {prof: rec.z_sum for prof, rec in sweep["classes"].items()
           if rec.z_sum < 0}
    assert got == NEG_CLASS_SUMS


def test_class_channels_are_monomials(sweep):
    """Structural: every class polynomial has exactly one exponent
    (weight c s^E is profile-determined), so class signs cannot cross
    over in s; and the class census matches the banked record."""
    classes = sweep["classes"]
    assert len(classes) == 260
    assert sum(1 for r in classes.values() if r.n_negative > 0) == 34
    for rec in classes.values():
        assert rec.poly == (
            {rec.exp: rec.z_sum * rec.coeff} if rec.z_sum else {})


def test_global_with_lower_sectors_all_positive(sweep):
    """The 80-monomial global sum (empty + singles + pairs + triples):
    every coefficient strictly positive, hence positive on (0,1)."""
    full = _global_poly(sweep["classes"])
    for k, v in lower_sector_poly().items():
        full[k] = full.get(k, Fraction(0)) + v
    full = {k: v for k, v in full.items() if v}
    assert len(full) == 80
    assert all(v > 0 for v in full.values())


def test_global_triples_at_one_half(sweep):
    """The 75-monomial triples-only global sum: all coefficients
    positive, the four negative-class exponents present, and the exact
    value at s = 1/2 matches the banked endpoint."""
    poly = _global_poly(sweep["classes"])
    assert len(poly) == 75
    assert all(v > 0 for v in poly.values())
    assert {136, 138, 148, 172} <= set(poly)
    half = Fraction(1, 2)
    assert sum(c * half**k for k, c in poly.items()) == \
        GLOBAL_TRIPLES_AT_HALF
