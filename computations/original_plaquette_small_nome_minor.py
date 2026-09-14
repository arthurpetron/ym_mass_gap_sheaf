"""Exact-rational pilot for the original extent-one plaquette minor.

Run: python3 -m computations.original_plaquette_small_nome_minor

Uses the existing corrected-slab geometry and unfixed quaternion variables.
The sparse pilot norm is NOT generally the Lean syntactic coefficient norm:
the companion Lean certificate must check the unreduced source expressions
independently. No pilot output enters Lean as an axiom or native oracle.
This is a finite-volume, fixed-nome candidate, not a physical mass-gap claim.
"""

from fractions import Fraction
from math import prod
import json

from computations.corrected_slab_haar_network import corrected_slab_haar_complex
from computations.exact_haar_network import (
    P_ONE, Poly, chi, holonomy, integrate_link, p_links, p_mul, p_var,
)


def coefficient_norm(p: Poly) -> Fraction:
    assert all(set(c).issubset({0}) for c in p.values())
    return sum((abs(c.get(0, Fraction(0))) for c in p.values()), Fraction(0))


def haar(p: Poly) -> Fraction:
    for link in sorted(p_links(p)):
        p = integrate_link(p, link)
    assert set(p).issubset({()})
    return p.get((), {}).get(0, Fraction(0))


def certificate_candidate() -> dict:
    complex_, faces, plaquettes = corrected_slab_haar_complex(1)
    lower_ids = tuple(i for i, (base, plane) in enumerate(plaquettes)
                      if base[3] == 0 and 3 not in plane)
    assert len(faces) == 72 and len(complex_.edges) == 116
    assert len(lower_ids) == 24 and lower_ids[0] == 0
    scalar_faces = tuple(holonomy(faces[i])[0] for i in lower_ids)
    assert all(len(f) == 64 for f in scalar_faces)
    radii = tuple(2 * coefficient_norm(f) + 1 for f in scalar_faces)
    probe = chi(1, holonomy(faces[0]))
    loop = dict(P_ONE)
    for link, _orientation in faces[0]:
        loop = p_mul(loop, p_var(link, 0))
    mixed = p_mul(probe, loop)
    norms = tuple(coefficient_norm(p) for p in (probe, mixed, P_ONE, loop))
    reference = tuple(haar(p) for p in (probe, mixed, P_ONE, loop))
    assert radii == (Fraction(129),) * 24
    assert norms == (128, 128, 1, 1)
    assert reference == (0, Fraction(1, 128), 1, 0)
    scalar_square = haar(p_mul(loop, loop))
    assert scalar_square == Fraction(1, 256)

    nome = Fraction(1, 1024)
    ratios = tuple(2 * nome**3 * radius for radius in radii)
    deltas = tuple(2 * ratio for ratio in ratios)
    error = prod(1 + delta for delta in deltas) - 1
    error_ceiling = Fraction(1, 65536)
    assert max(ratios) <= Fraction(1, 2)
    assert 0 < error <= error_ceiling
    probe_error = norms[0] * error_ceiling
    assert probe_error == Fraction(1, 512)
    assert reference[1] - probe_error >= Fraction(1, 256)
    assert reference[2] - error_ceiling >= Fraction(1, 2)
    assert reference[2] + error_ceiling <= 2
    assert error_ceiling <= Fraction(1, 2)
    determinant_upper = probe_error * Fraction(1, 2) - Fraction(1, 256) * Fraction(1, 2)
    assert determinant_upper == -Fraction(1, 1024)
    square_floor = determinant_upper**2
    weight = (2 * nome**3)**4
    assert 0 < weight <= 1
    # Coefficients of the collar-removed FULL-spectator OS reference.
    # Every amplitude/energy below still multiplies Zsp, not Haar(Lfar^2).
    reference_amplitudes = (Fraction(0), weight * reference[1] * scalar_square,
                            Fraction(1), Fraction(0))
    reference_energies = (Fraction(1), weight * scalar_square**2)
    full_spectator_determinant = -reference_amplitudes[1]
    full_spectator_budget = 2 * reference_energies[1]
    assert full_spectator_determinant == -weight / 32768
    assert full_spectator_budget == weight / 32768
    assert full_spectator_determinant**2 / full_spectator_budget == weight / 32768
    reference_energy_ceiling = Fraction(5)
    assert 2**2 + weight * Fraction(1, 2)**2 <= reference_energy_ceiling
    denominator_ceiling = 2 * reference_energy_ceiling + 1
    raw_floor = weight * square_floor / denominator_ceiling
    assert raw_floor > 0
    return {
        "scope": "original extent-one SU(2), fixed nome; Lean certification required",
        "lower_face_ids": lower_ids,
        "face_radii": radii,
        "probe_mixed_unit_loop_norms": norms,
        "reference_moments": reference,
        "scalar_square_moment": scalar_square,
        "collar_removed_amplitudes_per_Zsp": reference_amplitudes,
        "collar_removed_energies_per_Zsp": reference_energies,
        "collar_removed_determinant_per_Zsp_squared": full_spectator_determinant,
        "collar_removed_reference_budget_per_Zsp_cubed": full_spectator_budget,
        "nome": nome,
        "maximum_first_ratio": max(ratios),
        "face_delta": deltas[0],
        "exact_product_error": error,
        "error_ceiling": error_ceiling,
        "determinant_upper": determinant_upper,
        "determinant_square_floor": square_floor,
        "channel_weight": weight,
        "reference_energy_ceiling": reference_energy_ceiling,
        "denominator_ceiling": denominator_ceiling,
        "raw_reflected_norm_floor_candidate": raw_floor,
    }


if __name__ == "__main__":
    print(json.dumps(certificate_candidate(), default=str, indent=2))
