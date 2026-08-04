#!/usr/bin/env python3
"""Render and optionally update the BF4 five-cycle progress chart.

The default state is the hand-maintained JSON file
``docs/five-cycle-progress.json``.  A run always prints the resulting chart.
It contains both the detailed five-cycle campaign and the high-level path from
the current repository to the full Clay/Jaffe--Witten target.  Individual stage
states can be tested without changing the file:

    python3 scripts/five_cycle_progress.py --set haar5_evaluation=complete
    python3 scripts/five_cycle_progress.py --param raw_links=116

Parameter values use JSON syntax.  Add ``--write`` to persist the supplied
overrides after validation.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Final

REPO_ROOT: Final = Path(__file__).resolve().parent.parent
DEFAULT_STATE_PATH: Final = REPO_ROOT / "docs" / "five-cycle-progress.json"
VALID_STATUSES: Final = frozenset({"pending", "active", "complete", "blocked"})
STAGE_ORDER: Final = (
    ("carrier_adaptation", "116-link carrier adapted to 25 tree + 23 chords"),
    ("based_cycle_geometry", "rooted cycles fixed in order [0,4,5,6,10]"),
    ("haar_invariance", "degree-certified left/right Haar invariance"),
    ("unused_variable_integration", "111 unused Haar variables integrated"),
    ("cutoff_one_degree", "cutoff-one degrees certified [4,4,4,5,5]"),
    ("haar5_evaluation", "evaluate the two exact Haar_5 values"),
    ("haar5_comparison", "compare row and constant Haar_5 values"),
    ("centered_balance", "determine exact centered-vacuum balance"),
    ("lean_surface_certificate", "kernel-check rank-seven surface census and polynomials"),
    ("slab_surface_embedding", "embed 128 surfaces in literal 72-face / 116-link slab"),
    ("lean_centered_obstruction", "kernel-check strict centered normalization obstruction"),
    ("surface_haar_bridge", "prove closed-surface sum equals the actual Haar_5 moments"),
)
PROJECT_STAGE_ORDER: Final = (
    ("constructive_substrate", "constructive kernel, exact arithmetic, and audited proof infrastructure"),
    ("fixed_spacing", "fixed-spacing SU(2) heat-kernel Yang--Mills line"),
    ("haar5_surface_bridge", "BF4 Haar_5 surface expansion and topological amplitude"),
    ("frontier_bucket1", "FrontierDAG Bucket 1: a->0 gap-survival / cluster atoms"),
    ("frontier_bucket2", "FrontierDAG Bucket 2: reconstruction and physical-margin atoms"),
    ("functional_continuum", "a->0 Schwinger-functional limit with exact OS0--OS4"),
    ("uniform_spacing_floor", "one strictly-positive physical gap floor at every scale"),
    ("shared_physical_stack", "same-action pinned OS/GNS stack with gauge, AF, O(4), and nontriviality"),
    ("clay_target", "complete four-dimensional quantum Yang--Mills existence and mass-gap theorem"),
)
STATUS_MARKS: Final = {
    "pending": " ",
    "active": ">",
    "complete": "x",
    "blocked": "!",
}


def load_state(path: Path) -> dict[str, Any]:
    """Load and minimally validate one progress-state document."""
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("progress state must be a JSON object")
    stages = raw.get("stages")
    if not isinstance(stages, dict):
        raise ValueError("progress state requires a 'stages' object")
    expected = {stage for stage, _ in STAGE_ORDER}
    missing = expected.difference(stages)
    extra = set(stages).difference(expected)
    if missing or extra:
        raise ValueError(f"stage keys differ: missing={sorted(missing)}, extra={sorted(extra)}")
    invalid = {key: value for key, value in stages.items() if value not in VALID_STATUSES}
    if invalid:
        raise ValueError(f"invalid stage statuses: {invalid}")
    project_stages = raw.get("project_stages")
    if not isinstance(project_stages, dict):
        raise ValueError("progress state requires a 'project_stages' object")
    expected_project = {stage for stage, _ in PROJECT_STAGE_ORDER}
    missing_project = expected_project.difference(project_stages)
    extra_project = set(project_stages).difference(expected_project)
    if missing_project or extra_project:
        raise ValueError(
            "project stage keys differ: "
            f"missing={sorted(missing_project)}, extra={sorted(extra_project)}"
        )
    invalid_project = {
        key: value
        for key, value in project_stages.items()
        if value not in VALID_STATUSES
    }
    if invalid_project:
        raise ValueError(f"invalid project stage statuses: {invalid_project}")
    return raw


def apply_overrides(state: dict[str, Any], overrides: list[str]) -> None:
    """Apply validated ``stage=status`` overrides in place."""
    stages = state["stages"]
    project_stages = state["project_stages"]
    for override in overrides:
        if "=" not in override:
            raise ValueError(f"override must be stage=status: {override!r}")
        stage, status = override.split("=", maxsplit=1)
        if stage in stages:
            destination = stages
        elif stage in project_stages:
            destination = project_stages
        else:
            raise ValueError(f"unknown stage: {stage!r}")
        if status not in VALID_STATUSES:
            raise ValueError(f"invalid status {status!r}; choose from {sorted(VALID_STATUSES)}")
        destination[stage] = status


def apply_parameter_overrides(state: dict[str, Any], overrides: list[str]) -> None:
    """Apply validated ``parameter=json-value`` overrides in place."""
    parameters = state.get("parameters")
    if not isinstance(parameters, dict):
        raise ValueError("progress state requires a 'parameters' object")
    for override in overrides:
        if "=" not in override:
            raise ValueError(f"parameter override must be name=json-value: {override!r}")
        name, raw_value = override.split("=", maxsplit=1)
        if name not in parameters:
            raise ValueError(f"unknown parameter: {name!r}")
        try:
            parameters[name] = json.loads(raw_value)
        except json.JSONDecodeError as error:
            raise ValueError(
                f"invalid JSON value for parameter {name!r}: {raw_value!r}"
            ) from error


def _csv(values: object) -> str:
    if not isinstance(values, list):
        raise ValueError("chart list parameter is not a list")
    return ",".join(str(value) for value in values)


def _indented_atoms(values: object, prefix: str) -> list[str]:
    if not isinstance(values, list) or not all(isinstance(value, str) for value in values):
        raise ValueError("project atom parameter is not a list of strings")
    return [f"{prefix}{value}" for value in values]


def render_chart(state: dict[str, Any]) -> str:
    """Render a deterministic ASCII chart from the validated state."""
    parameters = state["parameters"]
    stages = state["stages"]
    evidence = state.get("evidence", {})
    project_stages = state["project_stages"]
    complete = sum(status == "complete" for status in stages.values())
    total = len(STAGE_ORDER)
    project_complete = sum(
        status == "complete" for status in project_stages.values()
    )
    project_total = len(PROJECT_STAGE_ORDER)
    lines = [
        "BF4 FIVE-BASED-CYCLE PROGRESS",
        "================================",
        f"progress: {complete}/{total} stages complete",
        "",
        f"Haar_{parameters['raw_links']} raw links",
        "        |",
        f"        v  {parameters['tree_links']} tree + {parameters['chords']} chords",
        f"adapted blocks [{_csv(parameters['adapted_blocks'])}]",
        f"        |  based cycles [{_csv(parameters['based_cycles'])}]",
        f"        |  raw blocks [{_csv(parameters['raw_blocks'])}]",
        f"        |  degrees [{_csv(parameters['incidence_degrees'])}]",
        f"        |  cycle space 2^{parameters['binary_cycle_rank']}"
        f" = {parameters['closed_surface_count']} closed surfaces",
        "        v",
        "Haar_5(row), Haar_5(constant)",
        "        |",
        "        v",
        "exact centered-vacuum balance",
        "        |",
        f"        v  {parameters['embedded_surface_count']}/"
        f"{parameters['closed_surface_count']} surfaces embedded",
        f"literal slab closure: {parameters['literal_slab_faces']} faces / "
        f"{parameters['raw_links']} links",
        f"incidence elimination: rank {parameters['slab_incidence_rank']} / "
        f"nullity {parameters['binary_cycle_rank']}",
        "        |",
        f"        v  exact {parameters['raw_links']} -> "
        f"{parameters['active_surface_links']} active links",
        f"selected surface factors: at most "
        f"{parameters['max_selected_surface_faces']} faces",
        f"primal graph: {parameters['surface_primal_vertices']} vertices / "
        f"{parameters['surface_primal_edges']} edges",
        "        |  128/128 maximal forests + rooted paths checked",
        "        v",
        "concrete chord-only forest-gauge evaluator",
        "        |  forest transport + remaining exact values open",
        "        |",
        "        v",
        "constructive surface-sum -> Haar_5 bridge",
        "",
        "STATUS PATH",
    ]
    for stage, label in STAGE_ORDER:
        status = stages[stage]
        lines.append(f"  [{STATUS_MARKS[status]}] {label} ({status})")
    lines.extend(
        [
            "",
            "evidence: "
            f"lean-bridge={evidence.get('lean_bridge_commit', '?')}  "
            f"evaluation={evidence.get('evaluation_commit', '?')}  "
            f"axiom-exceptions={evidence.get('axiom_exceptions', '?')}  "
            f"rust-cycles={evidence.get('rust_cycle_checks', '?')}",
            "certificate: "
            f"cycle-space={evidence.get('haar5_cycle_space', '?')}  "
            f"slab-embedding={evidence.get('slab_embedding', '?')}  "
            f"centered-defect={evidence.get('centered_defect', '?')}",
            "formal frontier: "
            f"surface-certificate={evidence.get('lean_surface_certificate', '?')}  "
            f"face-weight={evidence.get('surface_face_weight', '?')}  "
            f"haar-bridge={evidence.get('surface_haar_bridge', '?')}",
            "finite contraction: "
            f"qpoly={evidence.get('qpoly_assembly', '?')}  "
            f"six-face={evidence.get('six_face_sphere', '?')}",
            "orbit reduction: "
            f"haar={evidence.get('surface_orbit_haar', '?')}  "
            f"bivalence={evidence.get('surface_bivalence', '?')}",
            "forest gauge: "
            f"geometry={evidence.get('surface_primal_forests', '?')}  "
            f"lean-values={evidence.get('lean_forest_gauge_values', '?')}",
            "legend: [x] complete  [>] active  [ ] pending  [!] blocked",
        ]
    )
    lines.extend(
        [
            "",
            "WHOLE-PROJECT FORMAL ROADMAP: CURRENT LEAN -> COMPLETE YANG--MILLS PROOF",
            "========================================================================",
            f"high-level milestones: {project_complete}/{project_total} complete",
            "",
            "CURRENT CHECKED REPOSITORY",
            "        |",
            f"        [{STATUS_MARKS[project_stages['constructive_substrate']]}] "
            "constructive substrate + kernel/axiom guards",
            "        |",
            f"        [{STATUS_MARKS[project_stages['fixed_spacing']]}] "
            "fixed-spacing SU(2) heat-kernel Yang--Mills",
            "        |",
            f"        [{STATUS_MARKS[project_stages['haar5_surface_bridge']]}] "
            "active finite campaign: actual BF4 Haar_5 surface bridge",
            "            (supporting exact evidence; not alone a Clay closure)",
            "        |",
            "        +------------------------------+",
            "        |                              |",
            "        v                              v",
            f"[{STATUS_MARKS[project_stages['frontier_bucket1']]}] FRONTIERDAG BUCKET 1      "
            f"[{STATUS_MARKS[project_stages['frontier_bucket2']]}] FRONTIERDAG BUCKET 2",
        ]
    )
    bucket1 = _indented_atoms(parameters["frontier_bucket1_atoms"], "    - ")
    bucket2 = _indented_atoms(parameters["frontier_bucket2_atoms"], "    - ")
    width = max([len(line) for line in bucket1] + [1]) + 6
    for index in range(max(len(bucket1), len(bucket2))):
        left = bucket1[index] if index < len(bucket1) else ""
        right = bucket2[index] if index < len(bucket2) else ""
        lines.append(f"{left:<{width}}{right}")
    lines.extend(
        [
            "        |                              |",
            "        +---------------+--------------+",
            "                        v",
            "        canonical FrontierDAG atoms physically discharged",
            "                        |",
            "        +---------------+------------------+",
            "        |                                  |",
            "        v                                  v",
            f"[{STATUS_MARKS[project_stages['functional_continuum']]}] FUNCTIONAL CONTINUUM       "
            f"[{STATUS_MARKS[project_stages['uniform_spacing_floor']]}] UNIFORM GAP",
        ]
    )
    functional = _indented_atoms(parameters["functional_continuum_atoms"], "    - ")
    uniform = _indented_atoms(parameters["uniform_gap_atoms"], "    - ")
    width = max([len(line) for line in functional] + [1]) + 6
    for index in range(max(len(functional), len(uniform))):
        left = functional[index] if index < len(functional) else ""
        right = uniform[index] if index < len(uniform) else ""
        lines.append(f"{left:<{width}}{right}")
    lines.extend(
        [
            "        |                                  |",
            "        +----------------+-----------------+",
            "                         v",
            f"[{STATUS_MARKS[project_stages['shared_physical_stack']]}] SAME PHYSICAL STACK",
        ]
    )
    lines.extend(_indented_atoms(parameters["shared_stack_atoms"], "    - "))
    lines.extend(
        [
            "                         |",
            "                         v",
            f"[{STATUS_MARKS[project_stages['clay_target']]}] CLAY / JAFFE--WITTEN TARGET",
            f"    {parameters['final_goal']}",
            "",
            "PROJECT GATE STATUS",
        ]
    )
    for stage, label in PROJECT_STAGE_ORDER:
        status = project_stages[stage]
        lines.append(f"  [{STATUS_MARKS[status]}] {label} ({status})")
    lines.extend(
        [
            "",
            "honesty: this is the complete formal dependency roadmap, not a claim",
            "that the open milestones already have known proofs.",
            "[x] kernel-checked  [>] current work  [ ] genuinely open",
            "guarded frontier bundles remain deliberately uninhabited.",
        ]
    )
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, default=DEFAULT_STATE_PATH)
    parser.add_argument(
        "--set",
        action="append",
        default=[],
        metavar="STAGE=STATUS",
        help="override one stage; repeat as needed",
    )
    parser.add_argument(
        "--param",
        action="append",
        default=[],
        metavar="NAME=JSON",
        help="override one existing chart parameter; repeat as needed",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="persist validated --set overrides to the selected state file",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    state = load_state(args.state)
    apply_overrides(state, args.set)
    apply_parameter_overrides(state, args.param)
    if args.write:
        args.state.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
    print(render_chart(state))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
