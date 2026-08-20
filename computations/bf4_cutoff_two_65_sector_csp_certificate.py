"""Generate a finite CSP refutation for the cutoff-two 65-state sector.

The ternary variables are the 24 lower faces, the 24 fixed-interface faces,
and 24 auxiliary states of a three-state automaton.  Local constraints encode

* support of the fundamental-cube lower-link row,
* support of an arbitrary target lower-link row, and
* rejection of the language consisting of the fundamental cube together
  with all 0/2-labelled subsets of its six faces.

Unsatisfiability says that every target sharing a cube-supported boundary is
in that 65-state family.  The emitted search tree is untrusted; Lean rechecks
it with ``FiniteTernaryCSPUnsatCertificate``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from dataclasses import dataclass
from itertools import product
from typing import Iterable

from computations.bf4_cutoff_two_cube_boundary_row import CUBE_FACE_IDS
from computations.bf4_cutoff_two_krylov_edge_scout import (
    DOMAIN,
    EXPECTED_FIXED_FACE_IDS,
    EXPECTED_LOWER_FACE_IDS,
    LinkConstraint,
    lower_link_constraints,
)
from computations.exact_haar_network import invariant_multiplicity


AUXILIARY_IDS = tuple(range(1000, 1024))


@dataclass(frozen=True)
class Constraint:
    name: str
    scope: tuple[int, ...]
    allowed: tuple[tuple[int, ...], ...]


@dataclass(frozen=True)
class Conflict:
    constraint: int


@dataclass(frozen=True)
class Split:
    coordinate: int
    zero: "Certificate"
    one: "Certificate"
    two: "Certificate"


@dataclass(frozen=True)
class ForceZero:
    coordinate: int
    reject_one: int
    reject_two: int
    child: "Certificate"


@dataclass(frozen=True)
class ForceOne:
    coordinate: int
    reject_zero: int
    reject_two: int
    child: "Certificate"


@dataclass(frozen=True)
class ForceTwo:
    coordinate: int
    reject_zero: int
    reject_one: int
    child: "Certificate"


Certificate = Conflict | Split | ForceZero | ForceOne | ForceTwo


def _lean_index(index: int) -> str:
    """Name one shared, kernel-checked finite constraint index.

    Interning these indices avoids elaborating the identical ``Fin 121``
    bound proof tens of thousands of times throughout the generated tree.
    """

    return f"cutoffTwoCubeSubsetCSPConstraintIndex{index:03d}"


def _lean_index_declarations() -> list[str]:
    lines: list[str] = [
        "def cutoffTwoCubeSubsetCSPConstraintIndex (index : Fin 121) :",
        "    Fin cutoffTwoCubeSubsetCSPConstraints.length :=",
        "  ⟨index.val, by",
        "    rw [cutoffTwoCubeSubsetCSPConstraints_count]",
        "    exact index.isLt⟩",
        "",
    ]
    for index in range(121):
        lines.extend([
            f"def {_lean_index(index)} :",
            "    Fin cutoffTwoCubeSubsetCSPConstraints.length :=",
            "  cutoffTwoCubeSubsetCSPConstraintIndex",
            f"    ⟨{index}, by decide⟩",
            "",
        ])
    return lines


def _allowed_words(
    scope: tuple[int, ...], predicate,
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        word for word in product(DOMAIN, repeat=len(scope)) if predicate(word)
    )


def _cube_constraint(index: int, link: LinkConstraint) -> Constraint:
    scope = link.fixed_face_ids
    cube_labels = tuple(
        1 if EXPECTED_LOWER_FACE_IDS[variable] in CUBE_FACE_IDS else 0
        for variable in link.lower_variables
    )
    return Constraint(
        f"cube_link_{index}",
        scope,
        _allowed_words(
            scope,
            lambda word: invariant_multiplicity(cube_labels + word) > 0,
        ),
    )


def _target_constraint(index: int, link: LinkConstraint) -> Constraint:
    lower_scope = tuple(
        EXPECTED_LOWER_FACE_IDS[variable]
        for variable in link.lower_variables
    )
    scope = lower_scope + link.fixed_face_ids
    return Constraint(
        f"target_link_{index}",
        scope,
        _allowed_words(
            scope,
            lambda word: invariant_multiplicity(word) > 0,
        ),
    )


def _initial_automaton_constraint(face: int, auxiliary: int) -> Constraint:
    scope = (face, auxiliary)
    return Constraint(
        "classifier_initial",
        scope,
        _allowed_words(
            scope,
            lambda word: word[1] == (0 if word[0] == 1 else 1),
        ),
    )


def _transition(
    previous: int, label: int, *, cube_coordinate: bool,
) -> int:
    if previous == 2:
        return 2
    if cube_coordinate:
        if previous == 0:
            return 0 if label == 1 else 2
        return 1 if label in (0, 2) else 2
    return previous if label == 0 else 2


def _transition_constraint(
    index: int, previous: int, face: int, following: int,
    *, cube_coordinate: bool,
) -> Constraint:
    scope = (previous, face, following)
    return Constraint(
        f"classifier_step_{index}",
        scope,
        _allowed_words(
            scope,
            lambda word: word[2] == _transition(
                word[0], word[1], cube_coordinate=cube_coordinate
            ),
        ),
    )


def build_constraints() -> tuple[Constraint, ...]:
    links = lower_link_constraints()
    constraints: list[Constraint] = []
    constraints.extend(
        _cube_constraint(index, link) for index, link in enumerate(links)
    )
    constraints.extend(
        _target_constraint(index, link) for index, link in enumerate(links)
    )
    scan = CUBE_FACE_IDS + tuple(
        face for face in EXPECTED_LOWER_FACE_IDS if face not in CUBE_FACE_IDS
    )
    constraints.append(_initial_automaton_constraint(scan[0], AUXILIARY_IDS[0]))
    for index, face in enumerate(scan[1:], start=1):
        constraints.append(_transition_constraint(
            index,
            AUXILIARY_IDS[index - 1],
            face,
            AUXILIARY_IDS[index],
            cube_coordinate=face in CUBE_FACE_IDS,
        ))
    constraints.append(Constraint(
        "classifier_reject",
        (AUXILIARY_IDS[-1],),
        ((2,),),
    ))
    if len(constraints) != 121:
        raise AssertionError(f"expected 121 constraints, got {len(constraints)}")
    return tuple(constraints)


def _consistent(word: tuple[int, ...], scope: tuple[int, ...],
                assignment: dict[int, int]) -> bool:
    return all(
        coordinate not in assignment or assignment[coordinate] == label
        for coordinate, label in zip(scope, word, strict=True)
    )


@dataclass
class SearchStats:
    nodes: int = 0
    conflicts: int = 0
    splits: int = 0
    forces: int = 0
    maximum_depth: int = 0


def generate_certificate(
    constraints: tuple[Constraint, ...],
) -> tuple[Certificate, SearchStats]:
    variables = tuple(sorted({
        coordinate
        for constraint in constraints
        for coordinate in constraint.scope
    }))
    incident = {
        coordinate: tuple(
            index for index, constraint in enumerate(constraints)
            if coordinate in constraint.scope
        )
        for coordinate in variables
    }
    assignment: dict[int, int] = {}
    stats = SearchStats()

    def supporting_words(index: int) -> tuple[tuple[int, ...], ...]:
        constraint = constraints[index]
        return tuple(
            word for word in constraint.allowed
            if _consistent(word, constraint.scope, assignment)
        )

    def search(depth: int) -> Certificate:
        stats.nodes += 1
        stats.maximum_depth = max(stats.maximum_depth, depth)
        support_cache: dict[int, tuple[tuple[int, ...], ...]] = {}
        for index in range(len(constraints)):
            supported = supporting_words(index)
            support_cache[index] = supported
            if not supported:
                stats.conflicts += 1
                return Conflict(index)
        unassigned = tuple(
            coordinate for coordinate in variables if coordinate not in assignment
        )
        if not unassigned:
            raise AssertionError("the purportedly unsatisfiable CSP was satisfied")

        def rejection(coordinate: int, label: int) -> int | None:
            for index in incident[coordinate]:
                position = constraints[index].scope.index(coordinate)
                if not any(
                    word[position] == label for word in support_cache[index]
                ):
                    return index
            return None

        def score(coordinate: int) -> tuple[int, int, int]:
            possible = sum(
                rejection(coordinate, label) is None for label in DOMAIN
            )
            return (possible, -len(incident[coordinate]), coordinate)

        coordinate = min(unassigned, key=score)
        rejected = tuple(rejection(coordinate, label) for label in DOMAIN)
        possible = tuple(
            label for label, reject in enumerate(rejected) if reject is None
        )
        if len(possible) == 1:
            label = possible[0]
            assignment[coordinate] = label
            child = search(depth + 1)
            del assignment[coordinate]
            stats.forces += 1
            if label == 0:
                assert rejected[1] is not None and rejected[2] is not None
                return ForceZero(
                    coordinate, rejected[1], rejected[2], child
                )
            if label == 1:
                assert rejected[0] is not None and rejected[2] is not None
                return ForceOne(
                    coordinate, rejected[0], rejected[2], child
                )
            assert rejected[0] is not None and rejected[1] is not None
            return ForceTwo(coordinate, rejected[0], rejected[1], child)
        children: list[Certificate] = []
        stats.splits += 1
        for label in DOMAIN:
            assignment[coordinate] = label
            children.append(search(depth + 1))
        del assignment[coordinate]
        return Split(coordinate, children[0], children[1], children[2])

    certificate = search(0)
    return certificate, stats


def certificate_digest(certificate: Certificate) -> dict[str, int]:
    if isinstance(certificate, Conflict):
        return {
            "nodes": 1, "conflicts": 1, "splits": 0, "forces": 0,
            "depth": 0,
        }
    if isinstance(certificate, (ForceZero, ForceOne, ForceTwo)):
        child = certificate_digest(certificate.child)
        return {
            "nodes": 1 + child["nodes"],
            "conflicts": child["conflicts"],
            "splits": child["splits"],
            "forces": 1 + child["forces"],
            "depth": 1 + child["depth"],
        }
    children = tuple(certificate_digest(child) for child in (
        certificate.zero, certificate.one, certificate.two
    ))
    return {
        "nodes": 1 + sum(child["nodes"] for child in children),
        "conflicts": sum(child["conflicts"] for child in children),
        "splits": 1 + sum(child["splits"] for child in children),
        "forces": sum(child["forces"] for child in children),
        "depth": 1 + max(child["depth"] for child in children),
    }


def _lean_certificate(certificate: Certificate, indent: int = 2) -> str:
    space = " " * indent
    child_indent = indent + 2
    if isinstance(certificate, Conflict):
        return f"(.conflict {_lean_index(certificate.constraint)})"
    if isinstance(certificate, Split):
        return (
            f"(.split {certificate.coordinate}\n"
            f"{space}  {_lean_certificate(certificate.zero, child_indent)}\n"
            f"{space}  {_lean_certificate(certificate.one, child_indent)}\n"
            f"{space}  {_lean_certificate(certificate.two, child_indent)})"
        )
    if isinstance(certificate, ForceZero):
        return (
            f"(.forceZero {certificate.coordinate} "
            f"{_lean_index(certificate.reject_one)} "
            f"{_lean_index(certificate.reject_two)}\n"
            f"{space}  {_lean_certificate(certificate.child, child_indent)})"
        )
    if isinstance(certificate, ForceOne):
        return (
            f"(.forceOne {certificate.coordinate} "
            f"{_lean_index(certificate.reject_zero)} "
            f"{_lean_index(certificate.reject_two)}\n"
            f"{space}  {_lean_certificate(certificate.child, child_indent)})"
        )
    return (
        f"(.forceTwo {certificate.coordinate} "
        f"{_lean_index(certificate.reject_zero)} "
        f"{_lean_index(certificate.reject_one)}\n"
        f"{space}  {_lean_certificate(certificate.child, child_indent)})"
    )


def emit_lean(certificate: Certificate) -> str:
    return "\n".join([
        "/- Generated by the untrusted cutoff-two 65-sector CSP producer.",
        "   Lean rechecks every local conflict and forced/split branch. -/",
        "import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP",
        "",
        "namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificate",
        "",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 100000000",
        "",
        "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP",
        "open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate",
        "open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate.TernaryUnsatCertificate",
        "",
        *_lean_index_declarations(),
        "def cutoffTwoCubeSubsetCSPCertificate :",
        "    TernaryUnsatCertificate cutoffTwoCubeSubsetCSPConstraints.length :=",
        f"  {_lean_certificate(certificate)}",
        "",
        "theorem cutoffTwoCubeSubsetCSPCertificate_checked :",
        "    cutoffTwoCubeSubsetCSPCertificate.check",
        "      cutoffTwoCubeSubsetCSPConstraints [] = true := by",
        "  decide",
        "",
        "theorem cutoffTwoCubeSubsetCSP_unsatisfiable :",
        "    ¬ ∃ assignment : Nat → Nat,",
        "      AssignmentBounded assignment ∧",
        "      Satisfies cutoffTwoCubeSubsetCSPConstraints assignment := by",
        "  exact no_solution_of_check cutoffTwoCubeSubsetCSPConstraints",
        "    cutoffTwoCubeSubsetCSPCertificate",
        "    cutoffTwoCubeSubsetCSPCertificate_checked",
        "",
        "end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificate",
        "",
        "#print axioms",
        "  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificate.cutoffTwoCubeSubsetCSP_unsatisfiable",
        "",
    ])


@dataclass(frozen=True)
class CutSubcertificate:
    index: int
    certificate: Certificate
    bindings: tuple[tuple[int, int], ...]
    size: int


def _cut_certificate(
    certificate: Certificate, *, split_depth: int,
) -> tuple[str, tuple[CutSubcertificate, ...]]:
    cuts: list[CutSubcertificate] = []

    def walk(
        node: Certificate,
        bindings: tuple[tuple[int, int], ...],
        remaining_splits: int,
        indent: int,
    ) -> str:
        space = " " * indent
        child_indent = indent + 2
        if remaining_splits == 0 and not isinstance(node, Conflict):
            index = len(cuts)
            cuts.append(CutSubcertificate(
                index, node, bindings, certificate_digest(node)["nodes"]
            ))
            return f"cutoffTwoCubeSubsetCSPSubcertificate{index:03d}"
        if isinstance(node, Conflict):
            return f"(.conflict {_lean_index(node.constraint)})"
        if isinstance(node, Split):
            return (
                f"(.split {node.coordinate}\n"
                f"{space}  {walk(node.zero, ((node.coordinate, 0),) + bindings, remaining_splits - 1, child_indent)}\n"
                f"{space}  {walk(node.one, ((node.coordinate, 1),) + bindings, remaining_splits - 1, child_indent)}\n"
                f"{space}  {walk(node.two, ((node.coordinate, 2),) + bindings, remaining_splits - 1, child_indent)})"
            )
        if isinstance(node, ForceZero):
            return (
                f"(.forceZero {node.coordinate} "
                f"{_lean_index(node.reject_one)} "
                f"{_lean_index(node.reject_two)}\n"
                f"{space}  {walk(node.child, ((node.coordinate, 0),) + bindings, remaining_splits, child_indent)})"
            )
        if isinstance(node, ForceOne):
            return (
                f"(.forceOne {node.coordinate} "
                f"{_lean_index(node.reject_zero)} "
                f"{_lean_index(node.reject_two)}\n"
                f"{space}  {walk(node.child, ((node.coordinate, 1),) + bindings, remaining_splits, child_indent)})"
            )
        return (
            f"(.forceTwo {node.coordinate} "
            f"{_lean_index(node.reject_zero)} "
            f"{_lean_index(node.reject_one)}\n"
            f"{space}  {walk(node.child, ((node.coordinate, 2),) + bindings, remaining_splits, child_indent)})"
        )

    root = walk(certificate, (), split_depth, 2)
    return root, tuple(cuts)


def _lean_bindings(bindings: Iterable[tuple[int, int]]) -> str:
    return "[" + ", ".join(
        f"({coordinate}, {label})" for coordinate, label in bindings
    ) + "]"


def emit_sharded_lean(
    certificate: Certificate, *, output: Path, shard_count: int,
    split_depth: int,
) -> dict[str, int]:
    root_expression, cuts = _cut_certificate(
        certificate, split_depth=split_depth
    )
    bins: list[list[CutSubcertificate]] = [[] for _ in range(shard_count)]
    loads = [0] * shard_count
    for cut in sorted(cuts, key=lambda item: (-item.size, item.index)):
        shard = min(range(shard_count), key=lambda index: (loads[index], index))
        bins[shard].append(cut)
        loads[shard] += cut.size

    namespace = (
        "YMGap.Continuum."
        "BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificate"
    )
    module_prefix = (
        "YMGap.Continuum."
        "BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificateShard"
    )
    indices_module = (
        "YMGap.Continuum."
        "BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificateIndices"
    )
    indices_lines = [
        "/- Generated shared finite indices for the CSP certificate. -/",
        "import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP",
        "",
        f"namespace {namespace}",
        "",
        "set_option maxRecDepth 300000",
        "",
        "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP",
        "",
    ]
    indices_lines.extend(_lean_index_declarations())
    indices_lines.extend([f"end {namespace}", ""])
    indices_path = output.with_name(
        "BF4PhysicalBoundaryCutoffTwoCubeSubsetCSPCertificateIndices.lean"
    )
    indices_path.write_text("\n".join(indices_lines), encoding="utf-8")
    for shard, items in enumerate(bins):
        lines = [
            "/- Generated untrusted CSP refutation subtree data. -/",
            f"import {indices_module}",
            "",
            f"namespace {namespace}",
            "",
            "set_option maxRecDepth 1000000",
            "set_option maxHeartbeats 100000000",
            "",
            "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP",
            "open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate",
            "open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate.TernaryUnsatCertificate",
            "",
        ]
        for item in sorted(items, key=lambda entry: entry.index):
            name = f"cutoffTwoCubeSubsetCSPSubcertificate{item.index:03d}"
            lines.extend([
                f"def {name} :",
                "    TernaryUnsatCertificate cutoffTwoCubeSubsetCSPConstraints.length :=",
                f"  {_lean_certificate(item.certificate)}",
                "",
                f"theorem {name}_checked :",
                f"    {name}.check cutoffTwoCubeSubsetCSPConstraints",
                f"      {_lean_bindings(item.bindings)} = true := by",
                "  decide",
                "",
            ])
        lines.extend([f"end {namespace}", ""])
        shard_path = output.with_name(
            f"{output.stem}Shard{shard:02d}.lean"
        )
        shard_path.write_text("\n".join(lines), encoding="utf-8")

    root_lines = [
        "/- Generated root of the sharded cutoff-two 65-sector CSP proof. -/",
    ]
    root_lines.extend(
        f"import {module_prefix}{shard:02d}" for shard in range(shard_count)
    )
    root_lines.extend([
        "",
        f"namespace {namespace}",
        "",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 100000000",
        "",
        "open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetCSP",
        "open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate",
        "open YMGap.Continuum.FiniteTernaryCSPUnsatCertificate.TernaryUnsatCertificate",
        "",
        "def cutoffTwoCubeSubsetCSPCertificate :",
        "    TernaryUnsatCertificate cutoffTwoCubeSubsetCSPConstraints.length :=",
        f"  {root_expression}",
        "",
        "theorem cutoffTwoCubeSubsetCSPCertificate_checked :",
        "    cutoffTwoCubeSubsetCSPCertificate.check",
        "      cutoffTwoCubeSubsetCSPConstraints [] = true := by",
        "  simp only [cutoffTwoCubeSubsetCSPCertificate, check,",
    ])
    checked_names = [
        f"    cutoffTwoCubeSubsetCSPSubcertificate{cut.index:03d}_checked"
        + ("," if index + 1 < len(cuts) else "]")
        for index, cut in enumerate(cuts)
    ]
    root_lines.extend(checked_names)
    root_lines.extend([
        "  all_goals decide",
        "",
        "",
        "theorem cutoffTwoCubeSubsetCSP_unsatisfiable :",
        "    ¬ ∃ assignment : Nat → Nat,",
        "      AssignmentBounded assignment ∧",
        "      Satisfies cutoffTwoCubeSubsetCSPConstraints assignment := by",
        "  exact no_solution_of_check cutoffTwoCubeSubsetCSPConstraints",
        "    cutoffTwoCubeSubsetCSPCertificate",
        "    cutoffTwoCubeSubsetCSPCertificate_checked",
        "",
        f"end {namespace}",
        "",
        "#print axioms",
        f"  {namespace}.cutoffTwoCubeSubsetCSP_unsatisfiable",
        "",
    ])
    output.write_text("\n".join(root_lines), encoding="utf-8")
    return {
        "subcertificates": len(cuts),
        "shards": shard_count,
        "largest_shard_nodes": max(loads),
        "smallest_shard_nodes": min(loads),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stats", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--sharded", action="store_true")
    parser.add_argument("--shard-count", type=int, default=16)
    parser.add_argument("--split-depth", type=int, default=4)
    arguments = parser.parse_args()
    constraints = build_constraints()
    certificate, stats = generate_certificate(constraints)
    digest = certificate_digest(certificate)
    if digest != {
        "nodes": stats.nodes,
        "conflicts": stats.conflicts,
        "splits": stats.splits,
        "forces": stats.forces,
        "depth": stats.maximum_depth,
    }:
        raise AssertionError("certificate statistics drifted")
    if arguments.stats:
        print(json.dumps({
            "constraints": len(constraints),
            "variables": len({coordinate for constraint in constraints
                              for coordinate in constraint.scope}),
            **digest,
        }, sort_keys=True))
    if arguments.output is not None:
        if arguments.sharded:
            print(json.dumps(emit_sharded_lean(
                certificate,
                output=arguments.output,
                shard_count=arguments.shard_count,
                split_depth=arguments.split_depth,
            ), sort_keys=True))
        else:
            arguments.output.write_text(emit_lean(certificate), encoding="utf-8")


if __name__ == "__main__":
    main()
