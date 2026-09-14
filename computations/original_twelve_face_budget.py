"""Exact budget pilot, not an evaluation of the original YM numerator.

Uses the existing collar/heat/count formulas after small-support cancellation.
The ratio to the leading w^36 term is displayed to prevent mistaking this
absolute upper bound for the still-missing signed remainder bound.
"""

from fractions import Fraction
import json
import signal


def pilot():
    rows = []
    count_prefactor = 2**2 * 625**2
    assert count_prefactor == 1562500
    for denominator in (1024, 2048, 4096):
        w = Fraction(1, denominator)
        delta = 128 * w**3
        inverse_floor = 1 / (1 - delta)
        rate = 625 * (2 * delta + delta**2) * inverse_floor**48
        assert 0 < rate < 1
        prefactor = 8 * inverse_floor**96
        budget = prefactor * count_prefactor * rate**12 / (1 - rate)
        old_size_three = prefactor * count_prefactor * rate**3 / (1 - rate)
        assert 0 < budget < old_size_three
        assert budget > w**36
        rows.append({"nome_denominator": denominator,
                     "budget_approx": float(budget),
                     "budget_over_leading_approx": float(budget / w**36),
                     "improvement_over_size_three_approx": float(budget / old_size_three)})
    return {"minimum_size": 12, "count_prefactor": count_prefactor,
            "probe_link_count": 8, "probe_interval_caps": [2, 2], "rows": rows,
            "original_numerator_evaluated": False,
            "signed_remainder_or_positive_response_proved": False}


if __name__ == "__main__":
    signal.alarm(30)
    print(json.dumps(pilot(), separators=(",", ":")))
