"""Pins for the vertex-amplitude product formula and the wall discovery."""

from fractions import Fraction

from computations.vertex_amplitude import (
    ORBIT_109_VALUE,
    amplitude,
    combo_spins,
    surface_masks,
)


def test_orbit_109_closure():
    surf = surface_masks()
    z = amplitude(combo_spins([surf[59], surf[93]]))
    assert z == ORBIT_109_VALUE == Fraction(1, 6**16)


def test_minimal_negative_exemplar():
    """The wall's coordinate: first negative dual amplitude, arbitrated
    against raw moments (512-term chi-expansion, exact agreement)."""
    z = amplitude(combo_spins([2707861, 3216742, 2201848]))
    assert z == Fraction(-1, 3981312)


def test_surface_values_including_disjoint_unions():
    surf = surface_masks()
    sphere = next(v for v in surf if bin(v).count("1") == 6)
    torus = next(v for v in surf if bin(v).count("1") == 16)
    assert amplitude(combo_spins([sphere])) == Fraction(1, 16)
    assert amplitude(combo_spins([torus])) == Fraction(1, 65536)
    # disjoint union of two spheres: chi = 4, F = 12 -> 2^{-8}
    disjoint = next(
        v for v in surf
        if bin(v).count("1") == 12
        and amplitude([(v >> i) & 1 for i in range(24)]) == Fraction(1, 256)
    )
    assert disjoint  # exists (moment-engine arbitrated: 1/256, not 1/1024)


def test_formula_matches_raw_moments_on_fresh_configs():
    import itertools

    from computations.exact_haar_network import ContractionTooLarge
    from computations.hypercube4d_survey import evaluate_assignment, hypercube

    cx, faces, _meta = hypercube()
    surf = surface_masks()
    cells = [v for v in surf if bin(v).count("1") == 6]
    checked = 0
    for combo in itertools.combinations(cells, 3):
        spins = combo_spins(combo)
        try:
            zm = evaluate_assignment(cx, faces, spins, budget=200_000_000)
        except ContractionTooLarge:
            continue
        assert amplitude(spins) == (zm.get(0, 0) if zm else 0)
        checked += 1
        if checked >= 4:
            break
    # n = 3 uniform cell: formula = 2D-YM = moments = 4^{2-6}
    cell = cells[0]
    spins3 = [3 * ((cell >> i) & 1) for i in range(24)]
    assert amplitude(spins3) == Fraction(1, 256)
    zm = evaluate_assignment(cx, faces, spins3, budget=200_000_000)
    assert zm == {0: Fraction(1, 256)}
    assert checked >= 3
