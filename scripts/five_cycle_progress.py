#!/usr/bin/env python3
"""Render and optionally update the BF4 five-cycle progress chart.

The default state is the hand-maintained JSON file
``docs/five-cycle-progress.json``.  A run always prints the resulting chart.
Individual stage states can be tested without changing the file:

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
    return raw


def apply_overrides(state: dict[str, Any], overrides: list[str]) -> None:
    """Apply validated ``stage=status`` overrides in place."""
    stages = state["stages"]
    for override in overrides:
        if "=" not in override:
            raise ValueError(f"override must be stage=status: {override!r}")
        stage, status = override.split("=", maxsplit=1)
        if stage not in stages:
            raise ValueError(f"unknown stage: {stage!r}")
        if status not in VALID_STATUSES:
            raise ValueError(f"invalid status {status!r}; choose from {sorted(VALID_STATUSES)}")
        stages[stage] = status


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


def render_chart(state: dict[str, Any]) -> str:
    """Render a deterministic ASCII chart from the validated state."""
    parameters = state["parameters"]
    stages = state["stages"]
    evidence = state.get("evidence", {})
    complete = sum(status == "complete" for status in stages.values())
    total = len(STAGE_ORDER)
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
            f"commit={evidence.get('last_commit', '?')}  "
            f"axiom-exceptions={evidence.get('axiom_exceptions', '?')}  "
            f"rust-cycles={evidence.get('rust_cycle_checks', '?')}",
            "certificate: "
            f"cycle-space={evidence.get('haar5_cycle_space', '?')}  "
            f"centered-defect={evidence.get('centered_defect', '?')}",
            "legend: [x] complete  [>] active  [ ] pending  [!] blocked",
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
