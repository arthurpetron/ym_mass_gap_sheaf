#!/usr/bin/env python3
"""Render and optionally update the BF4 five-cycle progress chart.

The default state is the hand-maintained JSON file
``docs/five-cycle-progress.json``.  A run always prints the resulting chart.
It contains both the detailed five-cycle campaign and the high-level path from
the current repository to the full Clay/Jaffe--Witten target.  Individual stage
states can be tested without changing the file:

    python3 scripts/five_cycle_progress.py --set haar5_evaluation=complete
    python3 scripts/five_cycle_progress.py --compact
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
    (
        "constructive_substrate",
        "constructive kernel, exact arithmetic, and audited proof infrastructure",
    ),
    ("fixed_spacing", "fixed-spacing SU(2) heat-kernel Yang--Mills line"),
    ("haar5_surface_bridge", "BF4 Haar_5 surface expansion and topological amplitude"),
    ("frontier_bucket1", "FrontierDAG Bucket 1: a->0 gap-survival / cluster atoms"),
    ("frontier_bucket2", "FrontierDAG Bucket 2: reconstruction and physical-margin atoms"),
    ("functional_continuum", "a->0 Schwinger-functional limit with exact OS0--OS4"),
    ("uniform_spacing_floor", "one strictly-positive physical gap floor at every scale"),
    (
        "shared_physical_stack",
        "same-action pinned OS/GNS stack with gauge, AF, O(4), and nontriviality",
    ),
    ("clay_target", "complete four-dimensional quantum Yang--Mills existence and mass-gap theorem"),
)
WORK_GUIDE_ORDER: Final = (
    ("core_b_margin", "Core-B finite-s margin"),
    ("positive_exponent_compiler", "Positive-exponent certificate compiler"),
    ("finite_p2_cell", "Exact nonvacuous pΓ=2 finite cell"),
    ("fusion_phi_dictionary", "Fusion-spectrum/Phi trajectory dictionary theorem"),
    ("all_cutoff_bulk_control", "All-scale/cutoff CanonicalBulkControl family"),
    ("physical_pins", "Physical finePin + imagePin + fusionPower proofs"),
    ("tree_mayer_pentagon", "Tree/Mayer/pentagon frontier atoms"),
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
    work_guide = raw.get("work_guide")
    if not isinstance(work_guide, dict):
        raise ValueError("progress state requires a 'work_guide' object")
    expected_work = {stage for stage, _ in WORK_GUIDE_ORDER}
    missing_work = expected_work.difference(work_guide)
    extra_work = set(work_guide).difference(expected_work)
    if missing_work or extra_work:
        raise ValueError(
            "work-guide keys differ: "
            f"missing={sorted(missing_work)}, extra={sorted(extra_work)}"
        )
    invalid_work = {
        key: value for key, value in work_guide.items() if value not in VALID_STATUSES
    }
    if invalid_work:
        raise ValueError(f"invalid work-guide statuses: {invalid_work}")
    return raw


def apply_overrides(state: dict[str, Any], overrides: list[str]) -> None:
    """Apply validated ``stage=status`` overrides in place."""
    stages = state["stages"]
    project_stages = state["project_stages"]
    work_guide = state["work_guide"]
    for override in overrides:
        if "=" not in override:
            raise ValueError(f"override must be stage=status: {override!r}")
        stage, status = override.split("=", maxsplit=1)
        if stage in stages:
            destination = stages
        elif stage in project_stages:
            destination = project_stages
        elif stage in work_guide:
            destination = work_guide
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


def render_compact_work_guide(state: dict[str, Any]) -> str:
    """Render the live, compact dependency path used after each Lean run."""
    project = state["project_stages"]
    work_guide = state["work_guide"]
    lines = [
        "CURRENT CHECKED LEAN",
        "        |",
        f"        +-- [{STATUS_MARKS[project['constructive_substrate']]}] "
        "Constructive substrate and axiom guards",
        f"        +-- [{STATUS_MARKS[project['fixed_spacing']]}] "
        "Fixed-spacing SU(2) heat-kernel theory",
        f"        +-- [{STATUS_MARKS[project['haar5_surface_bridge']]}] "
        "BF4 Haar_5 surface bridge",
        "        |",
        "        v",
        f"[{STATUS_MARKS[project['frontier_bucket1']]}] FRONTIERDAG BUCKET 1",
        "        |",
    ]
    for key, label in WORK_GUIDE_ORDER:
        lines.append(f"        +-- [{STATUS_MARKS[work_guide[key]]}] {label}")
        if key == "all_cutoff_bulk_control":
            parameters = state["parameters"]
            lines.append(
                "        |     +-- [x] closed physical coordinates "
                f"{parameters['physical_coeff_closed_coordinate']}"
            )
            lines.append(
                "        |     +-- [x] physical coefficient prefix "
                f"k=[{_csv(parameters['physical_coeff_prefix_scales'])}] "
                f"({parameters['physical_coeff_prefix_atoms']} atoms)"
            )
            lines.append(
                "        |     +-- [>] exact coefficient tail "
                f"k>={parameters['physical_coeff_tail_start']}"
                + (" (pure-Nat boundary-free reserve family)"
                  if parameters.get("physical_coeff_half_time_interior_frontier")
                  else " (pure-Nat one-row strong-Turan family)"
                  if parameters.get("physical_coeff_half_time_turan_compiler")
                  else " (pure-Nat odd/even cross family)"
                  if parameters.get("physical_coeff_transition_compiler") else "")
            )
            lines.append(
                "        |     +-- [x] exact coefficient heads "
                f"k=[{_csv(parameters['physical_coeff_head_prefix_scales'])}]"
            )
            lines.append(
                "        |     +-- [x] all-cutoff head reduction "
                f"{parameters['physical_coeff_head_reduction']}"
            )
            if parameters.get("physical_coeff_head_boundary"):
                lines.append(
                    "        |     +-- [x] physical endpoint/debt boundary "
                    f"k>={parameters['physical_coeff_head_tail_start']}"
                )
            if parameters.get("physical_coeff_head_reverse_curvature"):
                lines.append(
                    "        |     +-- [x] physical broad-peak certificate "
                    f"{parameters['physical_coeff_head_reverse_curvature']}"
                )
            if parameters.get("physical_coeff_head_complete"):
                lines.append(
                    "        |     +-- [x] physical all-cutoff head seed "
                    f"k>={parameters['physical_coeff_head_tail_start']} "
                    "(Dirichlet energy + weighted-box consumer)"
                )
            else:
                lines.append(
                    "        |     +-- [>] residual head seed "
                    f"k>={parameters['physical_coeff_head_tail_start']}"
                )
            lines.append(
                "        |     +-- [x] parity proof compiler "
                f"{parameters['physical_coeff_tail_invariant']}"
            )
            if parameters.get("physical_coeff_transition_compiler"):
                lines.append(
                    "        |     +-- [x] transition proof-about-computation "
                    f"{parameters['physical_coeff_transition_compiler']}"
                )
            if parameters.get("physical_coeff_half_time_power_compiler"):
                lines.append(
                    "        |     +-- [x] half-time power compiler "
                    f"{parameters['physical_coeff_half_time_power_compiler']}"
                )
            if parameters.get("physical_coeff_half_time_parity_compiler"):
                lines.append(
                    "        |     +-- [x] heat-matched parity automaton "
                    f"{parameters['physical_coeff_half_time_parity_compiler']}"
                )
            if parameters.get("physical_coeff_half_time_heads"):
                lines.append(
                    "        |     +-- [x] heat-matched physical heads "
                    f"{parameters['physical_coeff_half_time_heads']}"
                )
            if parameters.get("physical_coeff_half_time_turan_compiler"):
                lines.append(
                    "        |     +-- [x] half-time Turan compression "
                    f"{parameters['physical_coeff_half_time_turan_compiler']}"
                )
            if parameters.get("physical_coeff_half_time_turan_obstruction"):
                lines.append(
                    "        |     +-- [!] fixed-w Turan shortcut retired "
                    f"{parameters['physical_coeff_half_time_turan_obstruction']}"
                )
            if parameters.get("physical_coeff_half_time_nat_frontier"):
                lines.append(
                    "        |     +-- [>] heat-matched pure-Nat frontier "
                    f"{parameters['physical_coeff_half_time_nat_frontier']}"
                )
            if parameters.get("physical_coeff_strand_reindex"):
                lines.append(
                    "        |     +-- [x] exact strand A1 reindex "
                    f"{parameters['physical_coeff_strand_reindex']}"
                )
            if parameters.get("physical_coeff_high_shift_tail"):
                lines.append(
                    "        |     +-- [x] physical high-shift half-time tail "
                    f"{parameters['physical_coeff_high_shift_tail']}"
                )
            if parameters.get("physical_coeff_half_time_balance"):
                lines.append(
                    "        |     +-- [x] half-time debt/reserve compiler "
                    f"{parameters['physical_coeff_half_time_balance']}"
                )
            if parameters.get("physical_coeff_half_time_head_discharged"):
                lines.append(
                    "        |     +-- [x] half-time boundary head "
                    f"{parameters['physical_coeff_half_time_head_discharged']}"
                )
            if parameters.get("physical_coeff_half_time_terminal_discharged"):
                lines.append(
                    "        |     +-- [x] half-time terminal shell "
                    f"{parameters['physical_coeff_half_time_terminal_discharged']}"
                )
            if parameters.get("physical_coeff_half_time_penultimate_discharged"):
                lines.append(
                    "        |     +-- [x] half-time penultimate shell "
                    f"{parameters['physical_coeff_half_time_penultimate_discharged']}"
                )
            if parameters.get("physical_coeff_half_time_antepenultimate_discharged"):
                lines.append(
                    "        |     +-- [x] half-time antepenultimate shell "
                    f"{parameters['physical_coeff_half_time_antepenultimate_discharged']}"
                )
            if parameters.get("physical_coeff_half_time_frontier"):
                lines.append(
                    "        |     +-- [>] half-time reserve frontier "
                    f"{parameters['physical_coeff_half_time_frontier']}"
                )
            lines.append(
                "        |     +-- [>] trapezoid + fine reserve "
                f"k>={parameters['physical_theta_tail_start']}"
            )
        if key == "physical_pins" and state["parameters"].get("physical_pins_head_free"):
            lines.append(
                "        |     +-- [x] all-cutoff head removed from physical carrier"
            )
            lines.append(
                "        |     +-- [x] finePin + imagePin + genuine Phi defect-power dictionary"
            )
            lines.append(
                "        |     +-- [>] pure-Nat interior reserve + theta tail inputs"
            )
    lines.extend(
        [
            "        |",
            "        v",
            f"[{STATUS_MARKS[project['frontier_bucket2']]}] FRONTIERDAG BUCKET 2",
            "        |",
            "        +-- edge shifts and physical-margin recursion",
            "        +-- bounded transfer Hamiltonian",
            "        +-- physical O(4) restoration",
            "        |",
            "        v",
            f"[{STATUS_MARKS[project['functional_continuum']]}] FUNCTIONAL CONTINUUM"
            f"  +  [{STATUS_MARKS[project['uniform_spacing_floor']]}] UNIFORM POSITIVE GAP",
            "        |",
            "        v",
            f"[{STATUS_MARKS[project['shared_physical_stack']]}] "
            "SAME-ACTION OS/GNS PHYSICAL STACK",
            "        |",
            "        v",
            f"[{STATUS_MARKS[project['clay_target']]}] "
            "CONSTRUCTIVE 4D YANG--MILLS EXISTENCE + MASS GAP",
            "",
            "[x] kernel-checked  [>] active  [ ] pending  [!] blocked",
        ]
    )
    return "\n".join(lines)


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
        "        |  all 127 nonempty mask values staged + kernel-checked",
        "        |  128/128 orientation-aware Haar ledgers checked",
        "        |  source degree-five + Haar invariance + cyclic words checked",
        "        |  physical factor/product lift kernel-checked",
        f"        |  word reducer: {evidence.get('surface_word_reducer', '?')}",
        f"        |  translation semantics: "
        f"{evidence.get('surface_translation_compiler', '?')}",
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
            f"lean-values={evidence.get('lean_forest_gauge_values', '?')}  "
            f"transport={evidence.get('surface_forest_translation', '?')}",
            "fusion path campaign: "
            f"ballot={evidence.get('fusion_ballot_closed_form', '?')}  "
            f"row-LC={evidence.get('fusion_path_row_logconcavity', '?')}  "
            f"weighted={evidence.get('fusion_weighted_interlacing', '?')}",
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
            "finite campaign: actual BF4 Haar_5 surface bridge",
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
    lines.append(
        "    current atom: "
        f"{parameters.get('current_frontier_atom', 'not selected')}"
    )
    lines.append("    completed supporting campaigns (not field inhabitants):")
    lines.extend(
        _indented_atoms(parameters["frontier_supporting_discharged"], "      [x] ")
    )
    lines.append("    physically discharged canonical fields:")
    lines.extend(
        _indented_atoms(parameters["frontier_discharged_atoms"], "      [x] ")
    )
    lines.append("    canonical fields still physically open:")
    lines.extend(
        _indented_atoms(parameters["frontier_open_atoms"], "      [ ] ")
    )
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
        "--compact",
        action="store_true",
        help="print only the compact live work guide",
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
    print(render_compact_work_guide(state) if args.compact else render_chart(state))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
