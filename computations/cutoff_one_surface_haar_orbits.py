"""Independent exact Haar audit of the cutoff-one surface orbit representatives.

The sparse BF4 surface certificate assigns a vacuum-to-surface amplitude
``2**(V-E)`` to every one of the 128 closed binary surfaces.  The surfaces
form nine hyperoctahedral orbits (vacuum included).  This module contracts one
literal quaternion spin network from each orbit and compares it with that
topological value using exact rational arithmetic.

This executable audit is evidence for the finite campaign, not a replacement
for the remaining constructive Lean proof that transports the representative
calculation uniformly across each orbit.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cache

from computations.exact_haar_network import P_ONE, chi
from computations.hypercube4d_surface_gram import build_surface_gram_survey
from computations.hypercube4d_survey import (
    exact_constant,
    hypercube,
    surface_cell_counts,
)


@dataclass(frozen=True)
class SurfaceHaarOrbitRecord:
    """One exact literal contraction and its predicted topological value."""

    representative: int
    orbit_size: int
    vertices: int
    edges: int
    faces: int
    euler: int
    exact_haar: Fraction
    topological_haar: Fraction

    @property
    def validates(self) -> bool:
        return self.exact_haar == self.topological_haar


@dataclass(frozen=True)
class CutoffOneSurfaceHaarOrbitAudit:
    """The nine representative checks covering all 128 binary surfaces."""

    records: tuple[SurfaceHaarOrbitRecord, ...]

    @property
    def covered_surface_count(self) -> int:
        return sum(record.orbit_size for record in self.records)

    @property
    def validated_orbit_count(self) -> int:
        return sum(record.validates for record in self.records)

    def validates(self) -> bool:
        return (
            len(self.records) == 9
            and self.covered_surface_count == 128
            and self.validated_orbit_count == len(self.records)
            and self.records[0].representative == 0
            and self.records[0].exact_haar == Fraction(1)
        )


@cache
def cutoff_one_surface_haar_orbit_audit() -> CutoffOneSurfaceHaarOrbitAudit:
    """Contract one exact fundamental-character network per surface orbit."""

    complex_, faces_list, _meta = hypercube()
    faces = tuple(faces_list)
    survey = build_surface_gram_survey()
    records: list[SurfaceHaarOrbitRecord] = []
    for orbit in survey.surface_orbits:
        representative = orbit[0]
        factors = [
            chi(1, complex_.holonomy_of(face))
            for face_index, face in enumerate(faces)
            if (representative >> face_index) & 1
        ]
        exact_haar = exact_constant(
            complex_.contract_invariant(factors or [dict(P_ONE)])
        )
        vertices, edges, face_count, euler = surface_cell_counts(
            complex_, faces, representative
        )
        records.append(
            SurfaceHaarOrbitRecord(
                representative=representative,
                orbit_size=len(orbit),
                vertices=vertices,
                edges=edges,
                faces=face_count,
                euler=euler,
                exact_haar=exact_haar,
                topological_haar=Fraction(2) ** (vertices - edges),
            )
        )
    audit = CutoffOneSurfaceHaarOrbitAudit(tuple(records))
    if not audit.validates():
        raise AssertionError("the cutoff-one surface Haar orbit audit failed")
    return audit


def render_surface_haar_orbit_audit(
    audit: CutoffOneSurfaceHaarOrbitAudit,
) -> str:
    """Render the exact orbit table used by the finite-campaign report."""

    lines = [
        "CUTOFF-ONE SURFACE HAAR ORBIT AUDIT",
        "====================================",
        "mask       orbit  (V,E,F,chi)  exact Haar  2^(V-E)  match",
    ]
    for record in audit.records:
        lines.append(
            f"0x{record.representative:06x}  {record.orbit_size:>5}  "
            f"({record.vertices:>2},{record.edges:>2},{record.faces:>2},"
            f"{record.euler:>2})  {str(record.exact_haar):>10}  "
            f"{str(record.topological_haar):>7}  "
            f"{'yes' if record.validates else 'NO'}"
        )
    lines.append(
        f"validated {audit.validated_orbit_count}/{len(audit.records)} orbits; "
        f"orbit census covers {audit.covered_surface_count}/128 surfaces"
    )
    return "\n".join(lines)
