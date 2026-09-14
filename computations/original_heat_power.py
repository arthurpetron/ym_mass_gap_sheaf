"""Exact finite heat-power pilot; signed residuals are not bounded here."""

from fractions import Fraction as F
from itertools import product
from math import prod
import json
import signal


def pilot():
    checks = 0
    extracted = 0
    nomes = [F(0), F(1, 3), F(-1, 2), F(1)]
    for length in range(6):
        for spins in product(range(4), repeat=length):
            degree = sum(s*(s+2) for s in spins)
            occupied = sum(s > 0 for s in spins)
            dimensions = prod(s+1 for s in spins)
            assert 3*occupied <= degree
            assert degree == 3*occupied + sum(s*(s+2)-3 if s else 0 for s in spins)
            for w in nomes:
                original = prod((s+1)*w**(s*(s+2)) for s in spins)
                assert original == dimensions*w**degree
                checks += 1
                if degree >= 36:
                    # Deliberately signed multiplier: this is not a positivity proof.
                    signed = F((-1)**sum(spins)*(length+1), length+2)
                    residual = dimensions*w**(degree-36)*signed
                    assert original*signed == w**36*residual
                    leading = dimensions*signed if degree == 36 else F(0)
                    higher = F(0) if degree == 36 else dimensions*w**(degree-37)*signed
                    assert residual == leading + w*higher
                    extracted += 1
    assert sum(s*(s+2) for s in [1]*12) == 36
    assert sum(s*(s+2) for s in [1]*11+[2]) == 41
    return {"exact_weight_products": checks, "division_free_signed_extractions": extracted,
            "nomes_include_zero_and_negative": True, "minimum_area": 12,
            "fundamental_heat_power": 36, "one_spin_two_heat_power": 41,
            "signed_leading_coefficient_and_remainder": "NOT BOUNDED",
            "positive_original_response": "NOT PROVED"}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
