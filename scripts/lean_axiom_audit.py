#!/usr/bin/env python3
"""Lean axiom-gate audit script (hashed-baseline format).

Enforces AGENTS.md Rule 1 in CI: no load-bearing theorem in the YMGap Lean
library may depend on an axiom outside the permitted gate `{propext,
Quot.sound}`, except for an explicitly reviewed entry in the EXCEPTIONS list.

# Why hashed

The previous baseline recorded one `name = axioms` line for EVERY theorem
(~7.5k lines / ~0.5 MB), growing linearly with declarations and forcing an
all-or-nothing regeneration on any change.  In practice ~100% of theorems are
clean (`⊆ {propext, Quot.sound}`), so that file was almost entirely redundant.

This version records instead:

  * an **EXCEPTIONS** list — the (few / zero) theorems that use an axiom
    OUTSIDE the gate, each human-readable and reviewable; and
  * a **NAMESPACE DIGESTS** table — one `namespace = <sha16>  (<count>)` line
    per namespace, a hash of that namespace's sorted canonical
    `name = union-of-observed-axioms` map.

CI stays fast, diffs are reviewable (a changed namespace touches one hash
line), and regeneration is per-namespace rather than whole-file.

# Usage

    python scripts/lean_axiom_audit.py            # check vs baseline
    python scripts/lean_axiom_audit.py --update   # regenerate baseline
    python scripts/lean_axiom_audit.py --strict   # also fail on namespace-digest drift
    python scripts/lean_axiom_audit.py --print-source-fingerprint
                                                # prepend this line to saved logs

Exit codes:
  0  -- clean (gate held; --strict: no digest drift).
  1  -- GATE FAIL: a theorem depends on an axiom outside the gate and is not
        a reviewed EXCEPTION (proof became non-constructive).
  2  -- (--strict) namespace-digest drift: some namespace's axiom profile
        changed (new/removed decls, or within-gate axiom changes).
  3  -- infrastructure error (build failed, no axiom info, missing baseline).

# Semantics

  * COMPLETENESS (all modes): the build log must contain the diagnostic from
    every executable ``#print axioms`` site in every source selected by the
    ``YMGap.*`` library.  Lake replays cached modules' saved info logs, so this
    remains complete on an incremental build; a truncated/partial log fails as
    an infrastructure error instead of silently weakening the gate. Any
    `PANIC` or internal-error diagnostic also fails closed even when Lake
    happens to return zero.
    Supplied logs additionally carry a SHA-256 fingerprint of the complete
    current default-build provenance: every selected Lean source (including
    both guard roots), toolchain/Lake inputs, the Make entry point, and the
    audit/import-selection scripts.  An otherwise complete stale log therefore
    cannot be replayed against a materially different build definition.
  * DEFAULT (`--`): the GATE check.  Fails only if a theorem depends on an
    axiom `∉ {propext, Quot.sound}` that is not in EXCEPTIONS.  Repeated
    canonical names are combined by union, so independently compiled
    colliding declarations cannot mask one another.  Within-gate
    changes, new theorems, and shrinks pass silently (they respect the gate).
    This matches AGENTS.md Rule 1 exactly.
  * STRICT (`--strict`): additionally the DIGEST check.  Fails if any
    namespace's canonical-name/unioned-axiom digest differs from the baseline.
    The compact baseline does not record historical source-site multiplicity;
    the complete live-log check above separately proves that the log covers
    every current site with its current multiplicity.  Use for deliberate
    review; regenerate with `--update`.

# Companion files / integration

  * `lean/AXIOM_AUDIT.md`         -- the hashed baseline (this script writes it).
  * `lean/AGENTS.md`             -- the constructivity contract Rule 1 enforces.
  * `scripts/frontier_status.py` -- reads the EXCEPTIONS list; clean decls default.
  * `make lean-audit[-strict|-update]`, `.github/workflows/lean-audit.yml`.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from lean_import_guard import (
    discover_main_sources,
    executable_text,
    load_lake_coverage,
    load_lake_manifest,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO_ROOT / "lean"
BASELINE_PATH = LEAN_DIR / "AXIOM_AUDIT.md"
SAFE_LEAN_BUILD = REPO_ROOT / "scripts" / "safe_lean_build.py"

# The permitted axiom gate (AGENTS.md Rule 1). Anything else => EXCEPTIONS.
GATE = frozenset({"propext", "Quot.sound"})

# --------------------------------------------------------------------------
# Lake-output parsing (unchanged shape — shared with frontier_status.py)
# --------------------------------------------------------------------------

THEOREM_PATTERN = re.compile(
    r"'(?P<name>[^\r\n]+?)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)"
)

# CSI covers the colour/control sequences Lake emits today; OSC and one-byte
# ANSI escapes are included as well so a supplied log cannot hide a marker by
# wrapping it in a different standard escape form.  Keep the historical export
# name because other static tooling imports it.
ANSI_CSI_PATTERN = re.compile(
    r"\x1b(?:\][^\x07]*(?:\x07|\x1b\\)|\[[0-?]*[ -/]*[@-~]|[@-_])"
)
SOURCE_GATE_PATTERN = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms\b")
ANY_GATE_PATTERN = re.compile(r"#print[ \t]+axioms\b")
SITE_THEOREM_PATTERN = re.compile(
    r"(?m)^(?:info:[ \t]+)?[^\r\n]*?"
    r"(?P<source>YMGap(?:/[^/:\r\n]+)*\.lean):"
    r"(?P<line>\d+):\d+:[ \t]*"
    r"'(?P<name>[^\r\n]+?)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)"
)
BUILD_FAILURE_PATTERN = re.compile(
    r"(?im)^(?:"
    r"[ \t]*error:[ \t]|"
    r"[^\r\n]*?:\d+:\d+:[ \t]+error:[ \t]|"
    r"[ \t]*✖[ \t]+\[[0-9]+/[0-9]+\]|"
    r"[ \t]*make(?:\[[0-9]+\])?:[ \t]+\*\*\*|"
    r"[ \t]*(?:fatal error|uncaught exception|killed)\b"
    r")[^\r\n]*$"
)
BUILD_SUCCESS_PATTERN = re.compile(
    r"(?m)^Build completed successfully(?: \([0-9]+ jobs?\))?\.?[ \t]*$"
)
INTERNAL_DIAGNOSTIC_PATTERN = re.compile(
    r"(?im)^[^\r\n]*(?:\bPANIC\b|\binternal(?:[ -]+compiler)?[ -]+error\b)[^\r\n]*$"
)
# Keep the established log label for compatibility; schema v2 below binds the
# entire default-build provenance, not only `.lean` source bytes.
SOURCE_FINGERPRINT_PREFIX = "YMGAP_SOURCE_FINGERPRINT"
SOURCE_FINGERPRINT_PATTERN = re.compile(
    rf"^{SOURCE_FINGERPRINT_PREFIX}[ \t]+sha256:(?P<digest>[0-9a-f]{{64}})$"
)


class BaselineFormatError(ValueError):
    """The hashed axiom baseline is absent, ambiguous, or malformed."""


class SourceInventoryError(RuntimeError):
    """The current full-build provenance cannot be fingerprinted completely."""


@dataclass(frozen=True)
class ValidatedAxiomLog:
    """A complete successful build log tied to the current source tree."""

    axioms: dict[str, set[str]]
    sites: Counter[tuple[str, int]]
    source_fingerprint: str


def normalize_build_log(output: str) -> str:
    """Remove ANSI controls and canonicalize all line endings."""
    return (
        ANSI_CSI_PATTERN.sub("", output)
        .replace("\r\n", "\n")
        .replace("\r", "\n")
    )


def is_project_decl_name(name: str) -> bool:
    """Recognize public and Lean-generated private declarations in YMGap."""
    return (
        name == "YMGap"
        or name.startswith("YMGap.")
        or name.startswith("_private.YMGap.")
    )


def _axiom_set(axioms_str: str | None) -> set[str]:
    if axioms_str is None:
        return set()
    return {a.strip() for a in axioms_str.split(",") if a.strip()}


def discover_axiom_gate_sites() -> tuple[
    Counter[tuple[str, int]], frozenset[str], tuple[str, ...]
]:
    """Enumerate executable source-level ``#print axioms`` commands.

    The import guard's lexer removes nested comments, line comments, and
    strings while preserving line breaks.  Requiring one command per line
    makes the source site unambiguous and lets the build-log audit fail closed
    by exact file and line, rather than by a compensable total count.
    """
    sources, source_issues = discover_main_sources()
    issues = list(source_issues)
    sites: Counter[tuple[str, int]] = Counter()
    source_names: set[str] = set()

    for path in sources.values():
        relative = path.relative_to(LEAN_DIR).as_posix()
        source_names.add(relative)
        try:
            clean = executable_text(path.read_text(encoding="utf-8"))
        except OSError as exc:
            issues.append(f"cannot read Lean source {relative}: {exc}")
            continue

        supported = list(SOURCE_GATE_PATTERN.finditer(clean))
        supported_starts = {match.start() for match in supported}
        for match in ANY_GATE_PATTERN.finditer(clean):
            if match.start() not in supported_starts:
                line = 1 + clean.count("\n", 0, match.start())
                issues.append(
                    f"unsupported axiom-gate placement at {relative}:{line}; "
                    "put one `#print axioms` command at the start of its own line"
                )
        for match in supported:
            line = 1 + clean.count("\n", 0, match.start())
            sites[(relative, line)] += 1

    return sites, frozenset(source_names), tuple(issues)


def _fingerprint_file_inventory(paths: Iterable[Path], *, root: Path) -> str:
    """Hash exact bytes under deterministic, root-relative, length framing.

    This small injectable core is also useful for adversarial static probes: a
    temporary guard or build-config input can be changed without touching the
    real repository, and the resulting digest must change.
    """
    records: dict[str, bytes] = {}
    issues: list[str] = []
    for path in paths:
        try:
            relative = path.relative_to(root).as_posix()
        except ValueError:
            issues.append(f"fingerprint path is outside repository root: {path}")
            continue
        if relative in records:
            issues.append(f"duplicate fingerprint path: {relative}")
            continue
        if not path.is_file():
            issues.append(f"missing/non-file fingerprint input: {relative}")
            continue
        try:
            records[relative] = path.read_bytes()
        except OSError as exc:
            issues.append(f"cannot read fingerprint input {relative}: {exc}")

    if issues:
        raise SourceInventoryError("; ".join(issues))

    digest = hashlib.sha256()
    digest.update(b"ymgap-full-build-provenance-v2\0")
    digest.update(len(records).to_bytes(8, "big"))
    for relative in sorted(records):
        payload = records[relative]
        for field in (relative.encode("utf-8"), payload):
            digest.update(len(field).to_bytes(8, "big"))
            digest.update(field)
    return digest.hexdigest()


def compute_source_fingerprint() -> str:
    """Hash every source and semantic input defining the default full build.

    The inventory comprises `YMGap.lean`, every `YMGap/**/*.lean` selected by
    the library glob, both default guard roots, and the explicit toolchain,
    Lake, Make, audit, and import-selection inputs above.  Required inputs fail
    closed when absent, and the Lake configuration/manifest must first pass the
    exact dependency-free build-shape guard; `lean/lakefile.lean` is included
    whenever it exists.
    """
    sources, source_issues = discover_main_sources()
    issues = list(source_issues)
    _, lake_shape_issues = load_lake_coverage()
    manifest_shape_issues = load_lake_manifest()
    issues.extend(f"invalid full-build Lake shape: {issue}" for issue in lake_shape_issues)
    issues.extend(
        f"invalid full-build Lake manifest: {issue}" for issue in manifest_shape_issues
    )
    if not YMGAP_PACKAGE_DIR.is_dir():
        issues.append(
            "missing required Lean package directory: "
            f"{YMGAP_PACKAGE_DIR.relative_to(REPO_ROOT)}"
        )
    if not sources:
        issues.append("default YMGap source inventory is empty")

    for path in REQUIRED_BUILD_PROVENANCE_PATHS:
        if not path.is_file():
            issues.append(
                "missing required full-build provenance input: "
                f"{path.relative_to(REPO_ROOT)}"
            )
    if issues:
        raise SourceInventoryError("; ".join(issues))

    optional_paths = tuple(
        path
        for path in OPTIONAL_BUILD_PROVENANCE_PATHS
        if path.exists() or path.is_symlink()
    )
    paths = tuple(sources.values()) + REQUIRED_BUILD_PROVENANCE_PATHS + optional_paths
    return _fingerprint_file_inventory(paths, root=REPO_ROOT)


def source_fingerprint_stamp(fingerprint: str | None = None) -> str:
    """Return the one-line provenance stamp accepted in supplied build logs."""
    value = fingerprint if fingerprint is not None else compute_source_fingerprint()
    if re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ValueError("provenance fingerprint must be a lowercase SHA-256 digest")
    return f"{SOURCE_FINGERPRINT_PREFIX} sha256:{value}"


def parse_source_fingerprint_stamp(clean_output: str) -> tuple[str | None, tuple[str, ...]]:
    """Parse exactly one well-formed source-fingerprint line from a clean log."""
    candidates = [
        line.strip()
        for line in clean_output.splitlines()
        if line.strip().startswith(SOURCE_FINGERPRINT_PREFIX)
    ]
    if not candidates:
        return None, (f"missing `{SOURCE_FINGERPRINT_PREFIX} sha256:<64 hex>` stamp",)
    if len(candidates) != 1:
        return None, (
            f"expected exactly one source-fingerprint stamp; found {len(candidates)}",
        )
    match = SOURCE_FINGERPRINT_PATTERN.fullmatch(candidates[0])
    if match is None:
        return None, (f"malformed source-fingerprint stamp: {candidates[0]!r}",)
    return match.group("digest"), ()


def parse_lake_output_with_sites(
    output: str,
) -> tuple[dict[str, set[str]], Counter[tuple[str, int]]]:
    """Parse canonical axiom profiles and their emitting source sites.

    Duplicate canonical names are combined by union.  This is conservative
    for deliberately colliding independently compiled modules: a forbidden
    axiom in either declaration cannot be hidden by a later clean occurrence.
    """
    clean_output = normalize_build_log(output)
    result: dict[str, set[str]] = {}
    sites: Counter[tuple[str, int]] = Counter()
    for match in SITE_THEOREM_PATTERN.finditer(clean_output):
        name = match.group("name")
        result.setdefault(name, set()).update(_axiom_set(match.group("axioms")))
        sites[(match.group("source"), int(match.group("line")))] += 1
    return result, sites


def parse_lake_output(output: str) -> dict[str, set[str]]:
    """Parse `lake build` output; return {theorem_name: set_of_axioms}."""
    result: dict[str, set[str]] = {}
    # Lean's formatter may wrap a long `#print axioms` declaration between
    # comma-separated axioms, for example `[propext,\n Quot.sound]`.  Search
    # the complete output instead of one physical line at a time so those
    # load-bearing declarations are not silently omitted from the audit.
    for m in THEOREM_PATTERN.finditer(normalize_build_log(output)):
        name = m.group("name")
        if is_project_decl_name(name):
            result.setdefault(name, set()).update(_axiom_set(m.group("axioms")))
    return result


def validate_complete_axiom_log(
    output: str,
    *,
    required_declarations: Iterable[str] = (),
) -> tuple[ValidatedAxiomLog | None, tuple[str, ...]]:
    """Validate successful, current, complete full-build axiom evidence.

    This is the single fail-closed supplied-log path shared by the axiom audit
    and the frontier report.  Besides normalizing ANSI/CR output, it rejects
    internal/failure diagnostics, requires Lake's terminal success marker and
    a unique current-build-provenance fingerprint, compares exact source-site
    multiplicities, and can require named declarations (the frontier's
    registered partial closes) to appear in the live map.
    """
    clean_output = normalize_build_log(output)
    issues: list[str] = []

    internal_diagnostics = [
        match.group(0).strip()
        for match in INTERNAL_DIAGNOSTIC_PATTERN.finditer(clean_output)
    ]
    for diagnostic in internal_diagnostics[:10]:
        issues.append(f"PANIC/internal-error diagnostic: {diagnostic}")
    if len(internal_diagnostics) > 10:
        issues.append(
            f"... and {len(internal_diagnostics) - 10} more internal diagnostics"
        )

    failure_diagnostics = [
        match.group(0).strip()
        for match in BUILD_FAILURE_PATTERN.finditer(clean_output)
    ]
    for diagnostic in failure_diagnostics[:10]:
        issues.append(f"Lake/Lean failure marker: {diagnostic}")
    if len(failure_diagnostics) > 10:
        issues.append(
            f"... and {len(failure_diagnostics) - 10} more failure markers"
        )

    terminal_line = next(
        (line for line in reversed(clean_output.splitlines()) if line.strip()),
        "",
    )
    if BUILD_SUCCESS_PATTERN.fullmatch(terminal_line) is None:
        issues.append(
            "log does not end with Lake's `Build completed successfully` marker"
        )

    stamped_fingerprint, stamp_issues = parse_source_fingerprint_stamp(clean_output)
    issues.extend(stamp_issues)
    try:
        current_fingerprint = compute_source_fingerprint()
    except SourceInventoryError as exc:
        current_fingerprint = ""
        issues.append(f"cannot fingerprint the current full-build provenance: {exc}")
    if (
        stamped_fingerprint is not None
        and current_fingerprint
        and stamped_fingerprint != current_fingerprint
    ):
        issues.append(
            "source-fingerprint mismatch: build log "
            f"{stamped_fingerprint}, current provenance {current_fingerprint}"
        )

    expected_sites, expected_sources, source_issues = discover_axiom_gate_sites()
    issues.extend(
        f"cannot establish source axiom-gate inventory: {issue}"
        for issue in source_issues
    )

    observed, observed_sites = parse_lake_output_with_sites(clean_output)
    if not observed:
        issues.append("no parseable source-located `#print axioms` diagnostics")

    invalid_names = sorted(name for name in observed if not is_project_decl_name(name))
    for name in invalid_names[:20]:
        issues.append(f"source axiom gate emitted non-YMGap name: {name}")
    if len(invalid_names) > 20:
        issues.append(f"... and {len(invalid_names) - 20} more non-YMGap names")

    unexpected_sources = sorted(
        source for source, _ in observed_sites if source not in expected_sources
    )
    for source in unexpected_sources[:20]:
        issues.append(f"axiom diagnostic came from non-current source: {source}")
    if len(unexpected_sources) > 20:
        issues.append(
            f"... and {len(unexpected_sources) - 20} more non-current sources"
        )

    missing_sites = expected_sites - observed_sites
    extra_sites = observed_sites - expected_sites
    if missing_sites:
        issues.append(
            f"missing {sum(missing_sites.values())} diagnostic(s) from current "
            f"source gate sites ({sum(expected_sites.values())} expected)"
        )
        for (source, line), count in sorted(missing_sites.items())[:20]:
            suffix = f" x{count}" if count != 1 else ""
            issues.append(f"missing source gate: {source}:{line}{suffix}")
        if len(missing_sites) > 20:
            issues.append(f"... and {len(missing_sites) - 20} more missing sites")
    if extra_sites:
        issues.append(
            f"found {sum(extra_sites.values())} stale/duplicate source-site "
            "diagnostic(s)"
        )
        for (source, line), count in sorted(extra_sites.items())[:20]:
            suffix = f" x{count}" if count != 1 else ""
            issues.append(f"stale/duplicate source gate: {source}:{line}{suffix}")
        if len(extra_sites) > 20:
            issues.append(f"... and {len(extra_sites) - 20} more extra sites")

    missing_declarations = sorted(set(required_declarations) - set(observed))
    for name in missing_declarations:
        issues.append(f"required live axiom declaration is absent: {name}")

    try:
        final_fingerprint = compute_source_fingerprint()
    except SourceInventoryError as exc:
        final_fingerprint = ""
        issues.append(f"cannot re-fingerprint current full-build provenance: {exc}")
    if current_fingerprint and final_fingerprint != current_fingerprint:
        issues.append(
            "full-build provenance changed while the log was being validated: "
            f"{current_fingerprint} -> {final_fingerprint}"
        )
    if (
        stamped_fingerprint is not None
        and final_fingerprint
        and stamped_fingerprint != final_fingerprint
        and stamped_fingerprint == current_fingerprint
    ):
        issues.append(
            "source-fingerprint mismatch after validation: build log "
            f"{stamped_fingerprint}, final provenance {final_fingerprint}"
        )

    if issues:
        return None, tuple(issues)
    assert stamped_fingerprint is not None
    return (
        ValidatedAxiomLog(observed, observed_sites, stamped_fingerprint),
        (),
    )


# --------------------------------------------------------------------------
# Namespace grouping + digests
# --------------------------------------------------------------------------


def namespace_of(name: str) -> str:
    """The declaration's enclosing namespace: name minus its last component."""
    return name.rsplit(".", 1)[0] if "." in name else name


def _canon_line(name: str, axioms: set[str]) -> str:
    return f"{name} = {', '.join(sorted(axioms))}"


def group_by_namespace(observed: dict[str, set[str]]) -> dict[str, list[str]]:
    groups: dict[str, list[str]] = {}
    for name in observed:
        groups.setdefault(namespace_of(name), []).append(name)
    return groups


def digest_of(names: list[str], observed: dict[str, set[str]]) -> str:
    body = "\n".join(_canon_line(n, observed[n]) for n in sorted(names))
    return hashlib.sha256(body.encode("utf-8")).hexdigest()[:16]


def compute_digests(observed: dict[str, set[str]]) -> dict[str, tuple[str, int]]:
    groups = group_by_namespace(observed)
    return {ns: (digest_of(names, observed), len(names)) for ns, names in groups.items()}


def exceptions_of(observed: dict[str, set[str]]) -> dict[str, set[str]]:
    return {n: ax - GATE for n, ax in observed.items() if ax - GATE}


def compare_reviewed_exceptions(
    observed: dict[str, set[str]],
    reviewed: dict[str, set[str]],
) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """Compare live forbidden axioms with the reviewed exception mapping.

    The first result contains live, outside-gate axioms that are not permitted
    by the reviewed record.  This is exactly the default axiom-audit gate
    semantics: a reviewed record may be a superset of the live forbidden
    axioms.  The second result contains the converse difference, namely
    reviewed exception axioms no longer present in the live profile.  Callers
    that claim the complete live log validates the exception baseline must
    reject *both* results; the ordinary gate audit rejects only the first and
    leaves broader profile drift to strict review.
    """
    live = exceptions_of(observed)
    unreviewed = {
        name: axioms - reviewed.get(name, set())
        for name, axioms in live.items()
        if axioms - reviewed.get(name, set())
    }
    stale = {
        name: axioms - live.get(name, set())
        for name, axioms in reviewed.items()
        if axioms - live.get(name, set())
    }
    return unreviewed, stale


# --------------------------------------------------------------------------
# Baseline read / write (hashed format)
# --------------------------------------------------------------------------

HEADER = """\
# Lean Axiom-Gate Audit Baseline (hashed)

> **Auto-maintained** by `scripts/lean_axiom_audit.py`.  Regenerate with
> `make lean-audit-update` after a full build.  CI (`make lean-audit`) enforces
> the gate; `make lean-audit-strict` additionally enforces the per-namespace
> digests.

Permitted axiom gate (AGENTS.md Rule 1): `{propext, Quot.sound}`.  Every
load-bearing theorem must stay within it, EXCEPT the reviewed entries in the
`## Exceptions` section below.  The `## Namespace digests` table is a compact,
per-namespace hash of the unique canonical `name = union-of-observed-axioms`
map, so that profile's drift is detected and regeneration is per-namespace (a
one-line diff), not whole-file.  This compact baseline does not record
historical source-site multiplicity; every complete live build log is instead
checked against the exact current sites and current multiplicities.

## Policy

  * **GATE FAIL** (`make lean-audit`): a theorem depends on an axiom outside
    `{propext, Quot.sound}` and is not listed under `## Exceptions`.
  * **DIGEST DRIFT** (`make lean-audit-strict`): a namespace's canonical-name /
    unioned-axiom digest differs from the recorded value (new/removed unique
    names or within-gate union shifts).  Review, then `make lean-audit-update`.

## Format

```
## Exceptions
<fully-qualified-name> = <comma-separated axioms outside the gate>   [# note]

## Namespace digests
<namespace> = <sha16>  (<decl-count>)
```

Lines starting with `#`/`>` and blanks are ignored.
"""

_BASELINE_NAME_ATOM = r"(?:YMGap|_private\.YMGap)(?:\.[A-Za-z0-9_']+)*"
_EXC_RE = re.compile(
    rf"^(?P<name>{_BASELINE_NAME_ATOM})\s*=\s*(?P<axioms>.+?)\s*$"
)
_DIG_RE = re.compile(
    rf"^(?P<ns>{_BASELINE_NAME_ATOM})\s*=\s*(?P<hash>[0-9a-f]{{16}})\s*"
    rf"\(\s*(?P<count>\d+)\s*\)\s*$"
)
_AXIOM_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")


def write_baseline(path: Path, observed: dict[str, set[str]]) -> None:
    exc = exceptions_of(observed)
    digests = compute_digests(observed)
    out = [HEADER, "", "## Exceptions", ""]
    if exc:
        for name in sorted(exc):
            out.append(_canon_line(name, exc[name]))
    else:
        out.append(
            "# (none — every tracked theorem is within {propext, Quot.sound})"
        )
    out += ["", "## Namespace digests", ""]
    for ns in sorted(digests):
        h, c = digests[ns]
        out.append(f"{ns} = {h}  ({c})")
    out.append("")
    path.write_text("\n".join(out), encoding="utf-8")


def parse_baseline(path: Path) -> tuple[dict[str, set[str]], dict[str, tuple[str, int]]]:
    """Return ``(exceptions, digests)`` from one valid hashed baseline.

    Missing sections, malformed data records, duplicate keys, non-sha16
    digests, absent/nonpositive counts, and non-outside-gate exception records
    raise :class:`BaselineFormatError`; none are silently skipped.
    """
    exc: dict[str, set[str]] = {}
    digests: dict[str, tuple[str, int]] = {}
    if not path.exists():
        raise BaselineFormatError(f"baseline does not exist: {path}")
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as exc_read:
        raise BaselineFormatError(f"cannot read baseline {path}: {exc_read}") from exc_read

    section: str | None = None
    section_counts = Counter()
    in_fence = False
    for line_number, line in enumerate(lines, 1):
        s = line.strip()
        if s.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if s == "## Exceptions":
            section_counts["exc"] += 1
            if section_counts["exc"] != 1:
                raise BaselineFormatError(
                    f"duplicate `## Exceptions` section at line {line_number}"
                )
            if section_counts["dig"]:
                raise BaselineFormatError(
                    f"`## Exceptions` occurs after digests at line {line_number}"
                )
            section = "exc"
            continue
        if s == "## Namespace digests":
            section_counts["dig"] += 1
            if section_counts["dig"] != 1:
                raise BaselineFormatError(
                    f"duplicate `## Namespace digests` section at line {line_number}"
                )
            if section_counts["exc"] != 1:
                raise BaselineFormatError(
                    f"digest section precedes exceptions at line {line_number}"
                )
            section = "dig"
            continue
        if s.startswith("## ") and section is not None:
            raise BaselineFormatError(
                f"unexpected section {s!r} at line {line_number}"
            )
        if not s or s.startswith("#") or s.startswith(">"):
            continue
        if section is None:
            # Human-readable header prose before the two machine sections.
            continue
        if section == "dig":
            m = _DIG_RE.match(s)
            if m is None:
                raise BaselineFormatError(
                    f"malformed namespace digest at line {line_number}: {s!r}"
                )
            namespace = m.group("ns")
            if namespace in digests:
                raise BaselineFormatError(
                    f"duplicate namespace digest {namespace!r} at line {line_number}"
                )
            count = int(m.group("count"))
            if count <= 0:
                raise BaselineFormatError(
                    f"nonpositive declaration count at line {line_number}: {count}"
                )
            digests[namespace] = (m.group("hash"), count)
            continue
        # Inline notes are permitted only after a syntactically complete record.
        record = s.split("#", 1)[0].rstrip()
        m = _EXC_RE.match(record)
        if m is None or not is_project_decl_name(m.group("name")):
            raise BaselineFormatError(
                f"malformed exception record at line {line_number}: {s!r}"
            )
        name = m.group("name")
        if name in exc:
            raise BaselineFormatError(
                f"duplicate exception {name!r} at line {line_number}"
            )
        raw_axioms = [item.strip() for item in m.group("axioms").split(",")]
        if any(not item or _AXIOM_NAME_RE.fullmatch(item) is None for item in raw_axioms):
            raise BaselineFormatError(
                f"malformed exception axiom list at line {line_number}: "
                f"{m.group('axioms')!r}"
            )
        axset = set(raw_axioms)
        if len(axset) != len(raw_axioms):
            raise BaselineFormatError(
                f"duplicate exception axiom at line {line_number}: "
                f"{m.group('axioms')!r}"
            )
        if axset & GATE:
            raise BaselineFormatError(
                f"exception {name!r} records permitted gate axioms at line "
                f"{line_number}: {', '.join(sorted(axset & GATE))}"
            )
        exc[name] = axset

    if in_fence:
        raise BaselineFormatError("unterminated Markdown code fence in baseline")
    if section_counts["exc"] != 1 or section_counts["dig"] != 1:
        raise BaselineFormatError(
            "hashed baseline must contain exactly one `## Exceptions` and one "
            "`## Namespace digests` section"
        )
    if not digests:
        raise BaselineFormatError("hashed baseline contains no namespace digests")
    return exc, digests


# --------------------------------------------------------------------------
# Build invocation
# --------------------------------------------------------------------------


def run_lake_build() -> tuple[int, str]:
    # The launcher owns concurrency, the cross-process build lock, and live
    # pressure/swap cutoffs.  Spool Lake output to disk so the Python audit
    # process does not retain a potentially large build log while Lean is at
    # peak memory.
    with tempfile.TemporaryDirectory(prefix="ymgap-lean-audit-") as directory:
        log_path = Path(directory) / "lake-build.log"
        proc = subprocess.run(
            [sys.executable, str(SAFE_LEAN_BUILD), "--log-file", str(log_path), "--"],
            cwd=REPO_ROOT,
            text=True,
            check=False,
        )
        output = log_path.read_text(encoding="utf-8", errors="replace") if log_path.exists() else ""
    return proc.returncode, output


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Lean axiom-gate audit (hashed baseline; enforces AGENTS.md Rule 1)."
    )
    parser.add_argument("--update", action="store_true",
                        help="Regenerate the hashed baseline from the current build.")
    parser.add_argument("--strict", action="store_true",
                        help="Also fail on per-namespace digest drift.")
    parser.add_argument("--from-file", type=Path, default=None,
                        help="Read `lake build` output from this file instead of running lake.")
    parser.add_argument(
        "--print-source-fingerprint",
        action="store_true",
        help="Print the current full-build provenance stamp and exit without building.",
    )
    args = parser.parse_args()

    if args.print_source_fingerprint:
        if args.from_file is not None or args.update or args.strict:
            parser.error(
                "--print-source-fingerprint cannot be combined with audit options"
            )
        try:
            print(source_fingerprint_stamp())
        except SourceInventoryError as exc:
            print(f"ERROR: cannot fingerprint full-build provenance: {exc}", file=sys.stderr)
            return 3
        return 0

    if args.from_file is not None:
        if not args.from_file.exists():
            print(f"ERROR: --from-file path does not exist: {args.from_file}", file=sys.stderr)
            return 3
        try:
            output = args.from_file.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as exc:
            print(f"ERROR: cannot read --from-file log: {exc}", file=sys.stderr)
            return 3
    else:
        rc, output = run_lake_build()
        if rc != 0:
            print(f"ERROR: lake build failed (exit {rc}).", file=sys.stderr)
            print(output, file=sys.stderr)
            return 3

    validated, log_issues = validate_complete_axiom_log(output)
    if log_issues:
        print("ERROR: rejected full-build axiom log:", file=sys.stderr)
        for issue in log_issues[:60]:
            print(f"  - {issue}", file=sys.stderr)
        if len(log_issues) > 60:
            print(f"  - ... and {len(log_issues) - 60} more", file=sys.stderr)
        return 3
    assert validated is not None
    observed = validated.axioms

    print(
        "Axiom-log completeness: PASS "
        f"({sum(validated.sites.values())} executable source gate sites; "
        f"provenance sha256:{validated.source_fingerprint})."
    )
    print()

    if args.update:
        write_baseline(BASELINE_PATH, observed)
        exc = exceptions_of(observed)
        digs = compute_digests(observed)
        print(f"Baseline updated: {len(observed)} theorems, {len(digs)} namespaces, "
              f"{len(exc)} exception(s) -> {BASELINE_PATH.relative_to(REPO_ROOT)}")
        return 0

    try:
        base_exc, base_dig = parse_baseline(BASELINE_PATH)
    except BaselineFormatError as exc:
        print(
            f"ERROR: invalid baseline {BASELINE_PATH.relative_to(REPO_ROOT)}: {exc}",
            file=sys.stderr,
        )
        return 3

    obs_exc = exceptions_of(observed)
    # GATE check: any theorem outside the gate must be a reviewed exception with
    # a superset-permitted record.
    unreviewed, _stale = compare_reviewed_exceptions(observed, base_exc)
    gate_fails = [
        f"  - {name}: axioms {{{', '.join(sorted(obs_exc[name]))}}} outside gate "
        f"{{propext, Quot.sound}}; unreviewed "
        f"{{{', '.join(sorted(extra))}}}"
        for name, extra in sorted(unreviewed.items())
    ]

    print(f"Lean axiom-gate audit: {len(observed)} theorems, "
          f"{len(group_by_namespace(observed))} namespaces, {len(obs_exc)} exception(s).")
    print()

    if gate_fails:
        print(f"GATE FAIL: {len(gate_fails)} theorem(s) depend on axioms outside the gate "
              f"and are not reviewed exceptions:")
        print("\n".join(gate_fails))
        print("\nAfter AGENTS.md Rule 1 review, add them under `## Exceptions` "
              "(or run `make lean-audit-update`).")
        return 1

    if args.strict:
        obs_dig = compute_digests(observed)
        drift: list[str] = []
        for ns in sorted(set(obs_dig) | set(base_dig)):
            o = obs_dig.get(ns)
            b = base_dig.get(ns)
            if o is None:
                drift.append(f"  - {ns}: removed (was {b[1]} decls)")
            elif b is None:
                drift.append(f"  - {ns}: NEW ({o[1]} decls)")
            elif o != b:
                drift.append(f"  - {ns}: digest {b[0]}({b[1]}) -> {o[0]}({o[1]})")
        if drift:
            print(f"STRICT: {len(drift)} namespace(s) drifted (axiom profile changed):")
            print("\n".join(drift))
            print("\nReview, then `make lean-audit-update` to accept.")
            return 2

    print("Axiom-gate audit: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
