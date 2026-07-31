"""Regression tests for the frontier-status truth hierarchy."""

from pathlib import Path

from scripts.frontier_status import (
    AxiomBaseline,
    bundle_state,
    parse_axiom_baseline,
    parse_guard_configuration,
)


def test_hashed_baseline_counts_clean_declarations(tmp_path: Path) -> None:
    baseline_path = tmp_path / "AXIOM_AUDIT.md"
    baseline_path.write_text(
        """
## Exceptions

# (none)

## Namespace digests

YMGap.Alpha = 0123456789abcdef  (17)
YMGap.Beta = fedcba9876543210  (23)
""",
        encoding="utf-8",
    )

    baseline = parse_axiom_baseline(baseline_path)

    assert isinstance(baseline, AxiomBaseline)
    assert baseline.exceptions == {}
    assert baseline.declaration_count == 40
    assert baseline.namespace_count == 2
    assert baseline.available


def test_hashed_baseline_keeps_reviewed_exceptions_separate(tmp_path: Path) -> None:
    baseline_path = tmp_path / "AXIOM_AUDIT.md"
    baseline_path.write_text(
        """
## Exceptions
YMGap.Alpha.bad = Classical.choice

## Namespace digests
YMGap.Alpha = 0123456789abcdef  (3)
""",
        encoding="utf-8",
    )

    baseline = parse_axiom_baseline(baseline_path)

    assert baseline.exceptions == {"YMGap.Alpha.bad": {"Classical.choice"}}
    assert baseline.declaration_count == 3


def test_guard_configuration_parses_protected_types_and_allowlist(
    tmp_path: Path,
) -> None:
    guard_path = tmp_path / "YMGapGuard.lean"
    guard_path.write_text(
        """
def frontierTypeNames : List Name :=
  [`YMGap.TargetA,
   `YMGap.TargetB]

def frontierAllowlist : List Name :=
  [`YMGap.reviewedClosure]
""",
        encoding="utf-8",
    )

    protected, allowlist = parse_guard_configuration(guard_path)

    assert protected == {"YMGap.TargetA", "YMGap.TargetB"}
    assert allowlist == {"YMGap.reviewedClosure"}


def test_guarded_state_does_not_depend_on_doc_markers() -> None:
    assert (
        bundle_state("YMGap.Target", {"YMGap.Target"}, [], [])
        == "**GUARDED OPEN**"
    )
    assert bundle_state("YMGap.Input", set(), [], []) == (
        "interface/input (not guard-verified)"
    )
