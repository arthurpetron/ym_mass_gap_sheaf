"""Regression gate for the exact cutoff-one surface-orbit Haar audit."""

from fractions import Fraction

from computations.cutoff_one_surface_haar_orbits import (
    cutoff_one_surface_haar_orbit_audit,
    render_surface_haar_orbit_audit,
)


def test_all_surface_orbit_representatives_have_topological_haar_value() -> None:
    audit = cutoff_one_surface_haar_orbit_audit()

    assert audit.validates()
    assert len(audit.records) == 9
    assert audit.covered_surface_count == 128
    assert audit.validated_orbit_count == 9
    assert {record.exact_haar for record in audit.records} == {
        Fraction(1),
        Fraction(1, 16),
        Fraction(1, 256),
        Fraction(1, 1024),
        Fraction(1, 4096),
        Fraction(1, 65536),
    }
    report = render_surface_haar_orbit_audit(audit)
    assert "validated 9/9 orbits" in report
    assert "covers 128/128 surfaces" in report
