#!/usr/bin/env python3
"""Frontier-status report generator.

Walks a DECLARED registry of frontier *bundle types* (the deliberately-open
`Type`-level targets that the continuum Yang–Mills program reduces to) and, for
each, reports:

  (a) its Lean type signature (parsed from the source module);
  (b) the current best partial close(s) — module + declaration name;
  (c) which fields / tokens remain OPEN (parsed from the structure body and
      classified by the doc-comment markers the codebase already uses);
  (d) the axiom gate of each partial close (from the recorded `#print axioms`
      baseline `lean/AXIOM_AUDIT.md`, or a fresh `lake build` log).

It also emits two whole-library audits:

  * an UNIMPORTED-FILE audit — every `YMGap/*.lean` NOT reachable (transitively)
    from `YMGap.lean`, i.e. silently skipped by the default build;
  * a NONCOMPUTABLE ledger — every `noncomputable` declaration.

The result is written to `docs/frontier-status.md` (dated).

# Usage

    python scripts/frontier_status.py                 # use AXIOM_AUDIT.md gates
    python scripts/frontier_status.py --from-file LOG  # gates from a build log
    python scripts/frontier_status.py --lake           # run `lake build` fresh
    python scripts/frontier_status.py --stdout         # print, don't write file

# Design (mirrors scripts/lean_axiom_audit.py)

The axiom-gate source of truth is the same recorded `#print axioms` data the
audit script maintains: `lean/AXIOM_AUDIT.md`.  Each partial-close declaration is
looked up there by fully-qualified name.  With `--from-file` / `--lake` the gates
are instead parsed live from a `lake build` log via the audit script's own
`THEOREM_PATTERN`, and layered OVER the baseline.  No file is edited; this script
is read-only w.r.t. the Lean sources.

This script does NOT prove anything and does NOT change the honest status.  It
distinguishes the frontier types protected by `YMGapGuard.lean` from unguarded
interfaces/inputs and treats source `OPEN` markers only as documentation.  It
reports partial closes and residual fields mechanically from the sources, guard
configuration, and axiom data.
"""

from __future__ import annotations

import argparse
import datetime
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import NotRequired, TypedDict

# --------------------------------------------------------------------------
# Paths
# --------------------------------------------------------------------------

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO_ROOT / "lean"
YMGAP_ROOT = LEAN_DIR / "YMGap.lean"
YMGAP_PKG = LEAN_DIR / "YMGap"
BASELINE_PATH = LEAN_DIR / "AXIOM_AUDIT.md"
OUTPUT_PATH = REPO_ROOT / "docs" / "frontier-status.md"
GUARD_PATH = LEAN_DIR / "YMGapGuard.lean"

# --------------------------------------------------------------------------
# Axiom-gate sources (shared shapes with lean_axiom_audit.py)
# --------------------------------------------------------------------------

# `#print axioms` build-log line shape (identical to lean_axiom_audit.py).
THEOREM_PATTERN = re.compile(
    r"'(?P<name>YMGap[\w\\.']+?)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)"
)

# `lean/AXIOM_AUDIT.md` recorded-baseline line shape.
BASELINE_LINE_RE = re.compile(r"^(?P<name>[^=#\s][^=]*?)\s*=\s*(?P<axioms>.*)$")
BASELINE_DIGEST_RE = re.compile(
    r"^(?P<namespace>YMGap[\w\\.']*?)\s*=\s*"
    r"(?P<digest>[0-9a-f]{8,64})\s*"
    r"(?:\(\s*(?P<count>\d+)\s*\))?\s*$"
)


@dataclass(frozen=True)
class AxiomBaseline:
    """The two logically different parts of the hashed axiom baseline.

    `exceptions` is a sparse map containing only declarations outside the
    constructive gate. `namespace_digests` carries the complete declaration
    inventory through per-namespace counts. Confusing the former with the latter
    caused the status report to claim that a clean baseline tracked zero
    declarations.
    """

    exceptions: dict[str, set[str]]
    namespace_digests: dict[str, tuple[str, int]]

    @property
    def declaration_count(self) -> int:
        return sum(count for _digest, count in self.namespace_digests.values())

    @property
    def namespace_count(self) -> int:
        return len(self.namespace_digests)

    @property
    def available(self) -> bool:
        return bool(self.exceptions or self.namespace_digests)


def parse_axiom_baseline(path: Path) -> AxiomBaseline:
    """Parse both sections of the hashed `AXIOM_AUDIT.md` baseline.

    The exception map is sparse; the digest map supplies the complete tracked
    declaration and namespace counts. For exact per-declaration axioms of clean
    declarations, run with `--from-file` or `--lake`.
    """
    exceptions: dict[str, set[str]] = {}
    digests: dict[str, tuple[str, int]] = {}
    if not path.exists():
        return AxiomBaseline(exceptions, digests)
    section: str | None = None
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("## Exceptions"):
            section = "exceptions"
            continue
        if stripped.startswith("## Namespace digests"):
            section = "digests"
            continue
        if not stripped or stripped.startswith(("#", ">")):
            continue
        if section == "digests":
            m_digest = BASELINE_DIGEST_RE.match(stripped)
            if m_digest:
                digests[m_digest.group("namespace")] = (
                    m_digest.group("digest"),
                    int(m_digest.group("count") or 0),
                )
            continue
        if section != "exceptions":
            continue
        m = BASELINE_LINE_RE.match(stripped)
        if not m:
            continue
        name = m.group("name").strip()
        if not name.startswith("YMGap"):
            continue
        exceptions[name] = {
            a.strip() for a in m.group("axioms").split(",") if a.strip()
        }
    return AxiomBaseline(exceptions, digests)


def parse_lake_output(output: str) -> dict[str, set[str]]:
    """Parse a `lake build` log into {name: axioms} (empty set = axiom-free)."""
    result: dict[str, set[str]] = {}
    # `#print axioms` output for long names may wrap inside the axiom list.
    # Match over the whole log so `[propext,\n Quot.sound]` remains visible.
    for m in THEOREM_PATTERN.finditer(output):
        axioms_str = m.group("axioms")
        result[m.group("name")] = (
            set() if axioms_str is None
            else {a.strip() for a in axioms_str.split(",") if a.strip()}
        )
    return result


def run_lake_build() -> tuple[int, str]:
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "3")
    proc = subprocess.run(
        ["lake", "build"], cwd=LEAN_DIR,
        capture_output=True, text=True, check=False,
        env=env,
    )
    return proc.returncode, proc.stdout + proc.stderr


def format_gate(name: str, gates: dict[str, set[str]]) -> str:
    """Human-readable axiom gate for a fully-qualified decl name."""
    if name not in gates:
        # Hashed baseline lists only out-of-gate EXCEPTIONS; an absent name is
        # within the gate.  (With --from-file/--lake, `gates` is the full live
        # map, so clean decls carry their exact axioms and never reach here.)
        return "within gate {propext, Quot.sound}"
    axset = gates[name]
    if not axset:
        return "axiom-free"
    return ", ".join(sorted(axset))


# --------------------------------------------------------------------------
# Lean-source parsing (structure signatures / fields; declaration modules)
# --------------------------------------------------------------------------

_TEXT_CACHE: dict[Path, str] = {}


def module_text(rel: str) -> str:
    """Read a module file (path relative to `lean/`), cached."""
    p = LEAN_DIR / rel
    if p not in _TEXT_CACHE:
        _TEXT_CACHE[p] = p.read_text(encoding="utf-8") if p.exists() else ""
    return _TEXT_CACHE[p]


# leading `n\t` cat -n style is NOT present in raw reads; work on raw lines.
DECL_KW = r"(?:structure|def|theorem|lemma|abbrev|inductive|class)"


def extract_signature(text: str, short_name: str) -> str:
    """Return the one-line-collapsed signature of a declaration.

    Captures from the `structure/def/... <short_name>` keyword through the end of
    the signature (the token `where` or `:=`, or a blank line), whichever first.
    """
    lines = text.splitlines()
    start = None
    pat = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?{DECL_KW}\s+{re.escape(short_name)}\b")
    for i, ln in enumerate(lines):
        if pat.search(ln):
            start = i
            break
    if start is None:
        return "(declaration not found)"
    chunk: list[str] = []
    for ln in lines[start:]:
        # stop tokens: `where` (structure body) or `:=` (a def body).
        m_where = re.search(r"\bwhere\b", ln)
        m_asgn = ln.find(":=")
        cut = ln
        stop = False
        if m_where and (m_asgn < 0 or m_where.start() < m_asgn):
            cut = ln[: m_where.start()]
            stop = True
        elif m_asgn >= 0:
            cut = ln[:m_asgn]
            stop = True
        chunk.append(cut.strip())
        if stop:
            break
        if ln.strip() == "" and chunk:
            break
    sig = " ".join(part for part in chunk if part)
    return re.sub(r"\s+", " ", sig).strip()


# Markers the codebase uses in field doc-comments to flag status.
OPEN_MARKERS = (
    "OPEN", "UNINHABITED", "NO inhabitant", "never proved", "never faked",
    "LEFT UNINHABITED", "not inhabited",
)
PROVED_MARKERS = (
    "PROVED", "CLOSED", "DERIVED", "CONVERGES", "genuine", "discharge",
    "re-export", "unconditional", "UNCONDITIONAL",
)


def classify(doc: str) -> str:
    """Classify a field as OPEN / PROVED / — from its doc-comment text."""
    up = doc
    if any(m.lower() in up.lower() for m in OPEN_MARKERS):
        return "OPEN"
    if any(m in up for m in PROVED_MARKERS):
        return "PROVED"
    return "—"


def extract_fields(text: str, struct_name: str) -> list[tuple[str, str, str]]:
    """Parse a `structure <name> ... where` body.

    Returns a list of (field_name, status, doc_first_sentence).  A field is an
    indented `ident :` line; the preceding `/-- ... -/` doc block (if any) is
    attached.  Stops at the next top-level `/-!`, `end`, `namespace`, or a
    non-indented declaration keyword.
    """
    lines = text.splitlines()
    # find `structure <name>` and its `where`.
    start = None
    pat = re.compile(rf"^\s*structure\s+{re.escape(struct_name)}\b")
    for i, ln in enumerate(lines):
        if pat.search(ln):
            start = i
            break
    if start is None:
        return []
    where_i = None
    for i in range(start, len(lines)):
        if re.search(r"\bwhere\b", lines[i]):
            where_i = i
            break
    if where_i is None:
        return []

    fields: list[tuple[str, str, str]] = []
    pending_doc: list[str] = []
    in_doc = False
    field_re = re.compile(r"^\s+(?P<fn>[a-zA-Z_][\w']*)\s*:")
    i = where_i + 1
    while i < len(lines):
        ln = lines[i]
        stripped = ln.strip()
        # end of the structure body.
        if re.match(r"^(?:/-!|end\b|namespace\b|structure\b|def\b|theorem\b"
                    r"|abbrev\b|inductive\b|@\[)", ln):
            break
        # doc-comment accumulation.
        if in_doc:
            pending_doc.append(stripped)
            if "-/" in stripped:
                in_doc = False
            i += 1
            continue
        if stripped.startswith("/--"):
            pending_doc = [stripped]
            in_doc = "-/" not in stripped
            i += 1
            continue
        m = field_re.match(ln)
        if m:
            doc = " ".join(pending_doc)
            doc = doc.replace("/--", "").replace("-/", "").strip()
            doc = re.sub(r"\s+", " ", doc)
            # first sentence, trimmed.
            first = re.split(r"(?<=[.;])\s", doc, maxsplit=1)[0] if doc else ""
            if len(first) > 140:
                first = first[:137] + "..."
            fields.append((m.group("fn"), classify(doc), first))
            pending_doc = []
        elif stripped == "":
            pending_doc = pending_doc  # keep doc across blank line
        i += 1
    return fields


def list_open_abbrevs(text: str, prefix: str = "Open") -> list[tuple[str, str]]:
    """Return (abbrev_name, underlying_type) for `abbrev <Prefix>...` decls."""
    out: list[tuple[str, str]] = []
    lines = text.splitlines()
    pat = re.compile(rf"^\s*abbrev\s+(?P<nm>{re.escape(prefix)}[\w']*)\b")
    for i, ln in enumerate(lines):
        m = pat.search(ln)
        if not m:
            continue
        # collect the whole abbrev (signature + RHS), stopping at the next
        # top-level decl / doc block / blank line, capped at 10 lines.
        chunk = []
        for j in range(i, min(i + 10, len(lines))):
            nxt = lines[j]
            if j > i and re.match(r"^\s*(?:abbrev|def|theorem|structure|/--|/-!|"
                                  r"end\b|namespace\b)", nxt):
                break
            if j > i and nxt.strip() == "":
                break
            chunk.append(nxt)
        joined = re.sub(r"\s+", " ", " ".join(chunk))
        rhs = joined.split(":=", 1)[1].strip() if ":=" in joined else ""
        if len(rhs) > 120:
            rhs = rhs[:117] + "..."
        out.append((m.group("nm"), rhs))
    return out


# --------------------------------------------------------------------------
# The DECLARED frontier registry
# --------------------------------------------------------------------------
# Each entry declares a frontier bundle TYPE, its module, the structure whose
# fields carry the open residual, and the best partial-close declarations.


class FrontierEntry(TypedDict):
    token: str
    type: str
    module: str
    struct: str
    partial_close: list[str]
    sub_structs: NotRequired[list[str]]
    open_abbrevs: NotRequired[str]


FRONTIER: list[FrontierEntry] = [
    {
        "token": "Tier0Scorecard atoms",
        "type": "YMGap.Continuum.Tier0Scorecard.Tier0Scorecard",
        "module": "YMGap/Continuum/Tier0Scorecard.lean",
        "struct": "Tier0Scorecard",
        # sub-bundles whose fields are the actual open atoms:
        "sub_structs": ["SubWallA"],
        "partial_close": [
            "YMGap.Continuum.Tier0Scorecard.fixedSpacing_met",
            "YMGap.Continuum.Tier0Scorecard.subA_offCorr_decompose",
            "YMGap.Continuum.Tier0Scorecard.subA_tree_graph",
            "YMGap.Continuum.Tier0Scorecard.subB_prodFloor_pos",
            "YMGap.Continuum.Tier0Scorecard.subB_physGap_pos",
            "YMGap.Continuum.Tier0Scorecard.toFrontierC",
        ],
    },
    {
        "token": "ReconstructionScorecardFinal tokens",
        "type": "YMGap.Rubric.ReconstructionScorecardFinal.ReconstructionOpenFrontier",
        "module": "YMGap/Rubric/ReconstructionScorecardFinal.lean",
        "struct": "ReconstructionOpenFrontier",
        "open_abbrevs": "Open",
        "partial_close": [
            "YMGap.Rubric.ReconstructionScorecardFinal.reconstruction_status",
            "YMGap.Rubric.ReconstructionScorecardFinal."
            "all_fixed_spacing_reconstruction_proved",
        ],
    },
    {
        "token": "UniformSpacingFloor",
        "type": "YMGap.Continuum.UnifiedContinuumFloor.UniformSpacingFloor",
        "module": "YMGap/Continuum/UnifiedContinuumFloor.lean",
        "struct": "UniformSpacingFloor",
        "partial_close": [
            "YMGap.Continuum.UnifiedContinuumFloor.ofUniformPhysGapFloor",
            "YMGap.Continuum.UnifiedContinuumFloor.ofModeEnergyFloor",
            "YMGap.Continuum.UnifiedContinuumFloor.ofContinuumGapPersistence",
            "YMGap.Continuum.UnifiedContinuumFloor.ofUniformRatioVariation",
            "YMGap.Continuum.UnifiedContinuumFloor.ofDimensionalTransmutation",
        ],
    },
    {
        "token": "SpectralMarginInput fields",
        "type": "YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput",
        "module": "YMGap/Continuum/AsymptoticSpectralLoc.lean",
        "struct": "SpectralMarginInput",
        "partial_close": [
            "YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.toAsymptotic",
            "YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput.uniform_floor",
            "YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput."
            "continuum_floor_pos",
        ],
    },
    {
        "token": "SixJPentagon",
        "type": "YMGap.Continuum.Tier0Scorecard.SixJPentagon",
        "module": "YMGap/Continuum/Tier0Scorecard.lean",
        "struct": "SixJPentagon",
        "partial_close": [
            "YMGap.Continuum.Tier0Scorecard.a2_racah",
            "YMGap.Continuum.Tier0Scorecard.a2_tetra_nonneg",
            "YMGap.Continuum.Tier0Scorecard.pentagon_to_racah",
        ],
    },
    {
        "token": "ClayTargetPinned",
        "type": "YMGap.Rubric.ClayTargetPinned.ClayTargetPinned",
        "module": "YMGap/Rubric/ClayTargetPinned.lean",
        "struct": "ClayTargetPinned",
        "partial_close": [
            "YMGap.Rubric.ClayTargetPinned.toClayTarget",
            "YMGap.Rubric.ClayTargetPinned.pinned_fixedSpacing_proved",
            "YMGap.Rubric.ClayTargetPinned.toClayTarget_fixedSpacing",
            "YMGap.Rubric.ClayTargetPinned.toClayTarget_o4_eq",
        ],
    },
    {
        "token": "ClayTarget",
        "type": "YMGap.Rubric.ClayScorecard.ClayTarget",
        "module": "YMGap/Rubric/ClayScorecard.lean",
        "struct": "ClayTarget",
        "partial_close": [
            "YMGap.Rubric.ClayScorecard.clay_fixed_spacing_met",
        ],
    },
    {
        "token": "FrontierDAG",
        "type": "YMGap.Rubric.FrontierDAG.FrontierDAG",
        "module": "YMGap/Rubric/FrontierDAG.lean",
        "struct": "FrontierDAG",
        "partial_close": [
            "YMGap.Rubric.FrontierDAG.toSubWallA",
            "YMGap.Rubric.FrontierDAG.trueMarginAtom",
            "YMGap.Rubric.FrontierDAG.o4Atom",
            "YMGap.Rubric.FrontierDAG.boundedHAtom",
        ],
    },
    {
        "token": "ContinuumYMExistence",
        "type": "YMGap.Continuum.FourDExistence.ContinuumYMExistence",
        "module": "YMGap/Continuum/FourDExistence.lean",
        "struct": "ContinuumYMExistence",
        "partial_close": [
            "YMGap.Continuum.FourDExistence.ym_mass_gap_of_existence",
        ],
    },
]


_BACKTICK_NAME_RE = re.compile(r"`([A-Za-z_][\w.]*)")


def _lean_name_list_body(text: str, def_name: str) -> str:
    """Return the bracket body of a simple Lean `List Name` definition."""
    start = text.find(f"def {def_name}")
    if start < 0:
        return ""
    open_bracket = text.find("[", start)
    if open_bracket < 0:
        return ""
    close_bracket = text.find("]", open_bracket)
    if close_bracket < 0:
        return ""
    return text[open_bracket + 1 : close_bracket]


def parse_guard_configuration(path: Path = GUARD_PATH) -> tuple[set[str], set[str]]:
    """Return `(protected frontier types, reviewed inhabitant allowlist)`.

    This is a static read of the guard configuration. The report deliberately
    tells users to compile `YMGapGuard` for the authoritative inhabitance check.
    """
    if not path.exists():
        return set(), set()
    text = path.read_text(encoding="utf-8")
    protected = set(
        _BACKTICK_NAME_RE.findall(_lean_name_list_body(text, "frontierTypeNames"))
    )
    allowlist = set(
        _BACKTICK_NAME_RE.findall(_lean_name_list_body(text, "frontierAllowlist"))
    )
    return protected, allowlist


def bundle_state(
    fq_type: str,
    guarded_types: set[str],
    open_fields: list[tuple[str, str, str]],
    open_abbrevs: list[tuple[str, str]],
) -> str:
    """Status label that never mistakes missing prose markers for closure."""
    if fq_type in guarded_types:
        return "**GUARDED OPEN**"
    if open_fields or open_abbrevs:
        return "**DECLARED OPEN**"
    return "interface/input (not guard-verified)"


def module_of(fq_name: str) -> str:
    """Map a fully-qualified decl to its module file.

    Prefers a `Namespace.name` (two-component) definition-site match to
    disambiguate common short names, then falls back to the bare short name.
    """
    parts = fq_name.split(".")
    short = parts[-1]
    two = ".".join(parts[-2:]) if len(parts) >= 2 else short
    # Tier 1: exact `def/... Namespace.name` (the dotted-definition form).
    pat_two = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?{DECL_KW}\s+"
                         rf"{re.escape(two)}\b")
    # Tier 2: any `def/... [qualifier.]name`.
    pat_one = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?{DECL_KW}\s+"
                         rf"(?:[\w.']+\.)?{re.escape(short)}\b")
    files = [f for f in sorted(YMGAP_PKG.rglob("*.lean")) if "/.lake/" not in str(f)]
    for pat in (pat_two, pat_one):
        for f in files:
            try:
                for ln in f.read_text(encoding="utf-8").splitlines():
                    if pat.search(ln):
                        return str(f.relative_to(LEAN_DIR))
            except OSError:
                continue
    return "(module not located)"


# --------------------------------------------------------------------------
# Unimported-file audit (transitive import closure from YMGap.lean)
# --------------------------------------------------------------------------

IMPORT_RE = re.compile(r"^\s*import\s+(YMGap[\w.]*)")


def module_to_file(mod: str) -> Path:
    return LEAN_DIR / (mod.replace(".", "/") + ".lean")


def file_to_module(path: Path) -> str:
    return str(path.relative_to(LEAN_DIR).with_suffix("")).replace("/", ".")


def imports_of_file(path: Path) -> list[str]:
    if not path.exists():
        return []
    out = []
    for ln in path.read_text(encoding="utf-8").splitlines():
        m = IMPORT_RE.match(ln)
        if m:
            out.append(m.group(1))
    return out


def import_closure() -> set[str]:
    """Transitive set of modules reachable from `YMGap.lean` (incl. root)."""
    seed = imports_of_file(YMGAP_ROOT)
    visited: set[str] = set()
    work = list(seed)
    while work:
        mod = work.pop()
        if mod in visited:
            continue
        visited.add(mod)
        f = module_to_file(mod)
        for dep in imports_of_file(f):
            if dep not in visited:
                work.append(dep)
    visited.add("YMGap")
    return visited


def unimported_files() -> list[str]:
    """`YMGap/*.lean` files whose module is NOT in the closure from YMGap.lean."""
    closure = import_closure()
    out = []
    for f in sorted(YMGAP_PKG.rglob("*.lean")):
        if "/.lake/" in str(f):
            continue
        mod = file_to_module(f)
        if mod not in closure:
            out.append(str(f.relative_to(LEAN_DIR)))
    return out


# --------------------------------------------------------------------------
# Noncomputable ledger
# --------------------------------------------------------------------------

NONCOMP_RE = re.compile(r"^\s*noncomputable\s+(?:def|abbrev|instance)\s+"
                        r"(?P<nm>[\w.']+)")


def noncomputable_ledger() -> list[tuple[str, int, str]]:
    """Return (module_rel, line_no, decl_name) for every noncomputable decl."""
    out: list[tuple[str, int, str]] = []
    for f in sorted(YMGAP_PKG.rglob("*.lean")):
        if "/.lake/" in str(f):
            continue
        try:
            lines = f.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for n, ln in enumerate(lines, 1):
            m = NONCOMP_RE.match(ln)
            if m:
                out.append((str(f.relative_to(LEAN_DIR)), n, m.group("nm")))
    return out


# --------------------------------------------------------------------------
# Report emission
# --------------------------------------------------------------------------


def emit_report(
    gates: dict[str, set[str]],
    gate_source: str,
    guarded_types: set[str] | None = None,
    guard_allowlist: set[str] | None = None,
) -> str:
    guarded_types = guarded_types or set()
    guard_allowlist = guard_allowlist or set()
    today = datetime.date.today().isoformat()
    L: list[str] = []  # noqa: N806 - compact report-builder notation
    A = L.append  # noqa: N806 - compact report-builder notation

    A("# Frontier status")
    A("")
    A(f"> **Auto-generated** by `scripts/frontier_status.py` on {today}.")
    A(f"> Axiom-gate source: {gate_source}.")
    A(f"> Guard configuration: **{len(guarded_types)} protected frontier types**, "
      f"**{len(guard_allowlist)} reviewed allowlist entries**.")
    A("> Read-only report — no Lean source is edited. `GUARDED OPEN` is determined")
    A("> from `YMGapGuard.lean`; field counts are only documentation-marker counts.")
    A("")
    A("The Clay Yang–Mills mass-gap problem remains **OPEN**. This document is a")
    A("status ledger, not a claim of closure. Run `make lean-frontier-guard` for")
    A("the authoritative environment-level inhabitance check.")
    A("")

    # --- Summary table ---
    A("## Summary")
    A("")
    A("| Frontier bundle | Lean type | theorem state | # partial closes | "
      "# doc-marked OPEN fields |")
    A("|---|---|---|---|---|")
    summary_rows = []
    per_entry = []
    for e in FRONTIER:
        text = module_text(e["module"])
        fields = extract_fields(text, e["struct"])
        # include sub-structs' fields as open atoms.
        for sub in e.get("sub_structs", []):
            fields += extract_fields(text, sub)
        open_fields = [f for f in fields if f[1] == "OPEN"]
        open_abbrevs = []
        if "open_abbrevs" in e:
            open_abbrevs = list_open_abbrevs(text, e["open_abbrevs"])
        n_open = len(open_fields) + len(open_abbrevs)
        per_entry.append((e, text, fields, open_fields, open_abbrevs))
        short_type = e["type"].rsplit(".", 1)[-1]
        state = bundle_state(e["type"], guarded_types, open_fields, open_abbrevs)
        summary_rows.append(
            f"| {e['token']} | `{short_type}` | {state} | "
            f"{len(e['partial_close'])} | {n_open} |"
        )
    L.extend(summary_rows)
    A("")

    # --- Per-bundle sections ---
    for e, text, fields, open_fields, open_abbrevs in per_entry:
        A(f"## {e['token']}")
        A("")
        sig = extract_signature(text, e["struct"])
        A(f"**(a) Lean type** — `{e['type']}`")
        A("")
        A(f"module `lean/{e['module']}`")
        state = bundle_state(e["type"], guarded_types, open_fields, open_abbrevs)
        A(f"theorem state: {state}")
        A("")
        A("```lean")
        A(sig)
        A("```")
        A("")

        A("**(b) Best partial close(s)** — module + decl + (d) axiom gate:")
        A("")
        A("| decl | module | axiom gate |")
        A("|---|---|---|")
        for pc in e["partial_close"]:
            short = pc.rsplit(".", 1)[-1]
            mod = module_of(pc)
            gate = format_gate(pc, gates)
            A(f"| `{short}` | `lean/{mod}` | {gate} |")
        A("")

        A("**(c) Fields explicitly marked OPEN in source documentation:**")
        A("")
        if open_fields:
            for fn, _st, doc in open_fields:
                doc_s = f" — {doc}" if doc else ""
                A(f"- `{fn}`{doc_s}")
        if open_abbrevs:
            for nm, rhs in open_abbrevs:
                A(f"- `{nm}` = `{rhs}`")
        if not open_fields and not open_abbrevs:
            A("- (none; absence of an `OPEN` marker does **not** prove that the")
            A("  structure is inhabited or that its physical hypotheses are discharged)")
        A("")

        # full field ledger for transparency.
        if fields:
            A("<details><summary>full field ledger (documentation markers only)</summary>")
            A("")
            A("| field | status | doc |")
            A("|---|---|---|")
            for fn, st, doc in fields:
                A(f"| `{fn}` | {st} | {doc} |")
            A("")
            A("</details>")
            A("")

    # --- Unimported-file audit ---
    A("## Unimported-file audit")
    A("")
    A("Every `YMGap/*.lean` NOT reachable (transitively) from `YMGap.lean` — i.e.")
    A("silently skipped by the default `lake build` and therefore un-audited.")
    A("")
    unimp = unimported_files()
    total = sum(1 for f in YMGAP_PKG.rglob("*.lean") if "/.lake/" not in str(f))
    A(f"Reachable modules parsed from import closure; **{len(unimp)} of {total}** "
      f"`YMGap/*.lean` files are unreachable from `YMGap.lean`.")
    A("")
    if unimp:
        for f in unimp:
            A(f"- `lean/{f}`")
    else:
        A("- (none — every `YMGap/*.lean` is reachable from `YMGap.lean`)")
    A("")

    # --- Noncomputable ledger ---
    A("## Noncomputable ledger")
    A("")
    A("Every `noncomputable def/abbrev/instance` in `YMGap/`. These do not compile")
    A("to executable code (they rest on `Q'`/data that Lean cannot evaluate) but")
    A("remain type-checked and axiom-gated.")
    A("")
    nc = noncomputable_ledger()
    A(f"**{len(nc)}** noncomputable declaration(s).")
    A("")
    if nc:
        A("| module | line | decl |")
        A("|---|---|---|")
        for mod, ln, nm in nc:
            A(f"| `lean/{mod}` | {ln} | `{nm}` |")
    else:
        A("- (none)")
    A("")

    return "\n".join(L) + "\n"


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description="Generate docs/frontier-status.md.")
    ap.add_argument("--from-file", type=Path, default=None,
                    help="Layer axiom gates from this `lake build` log over the baseline.")
    ap.add_argument("--lake", action="store_true",
                    help="Run `lake build` and layer its axiom gates over the baseline.")
    ap.add_argument("--stdout", action="store_true",
                    help="Print the report to stdout instead of writing the file.")
    args = ap.parse_args()

    baseline = parse_axiom_baseline(BASELINE_PATH)
    gates = dict(baseline.exceptions)
    gate_source = (
        "`lean/AXIOM_AUDIT.md` hashed baseline "
        f"({baseline.declaration_count} tracked declarations, "
        f"{baseline.namespace_count} namespaces, "
        f"{len(baseline.exceptions)} reviewed exceptions)"
    )
    if not baseline.available:
        print(f"WARNING: baseline {BASELINE_PATH} empty/missing; gates unavailable.",
              file=sys.stderr)

    live = None
    if args.from_file is not None:
        if not args.from_file.exists():
            print(f"ERROR: --from-file not found: {args.from_file}", file=sys.stderr)
            return 3
        live = parse_lake_output(args.from_file.read_text(encoding="utf-8"))
        live_namespaces = {name.rsplit(".", 1)[0] for name in live}
        gate_source = (
            f"`{args.from_file}` build log "
            f"({len(live)} declarations, {len(live_namespaces)} namespaces; "
            "layered over AXIOM_AUDIT.md)"
        )
    elif args.lake:
        returncode, output = run_lake_build()
        if returncode != 0:
            print(f"ERROR: lake build failed (exit {returncode}).", file=sys.stderr)
            return 3
        live = parse_lake_output(output)
        live_namespaces = {name.rsplit(".", 1)[0] for name in live}
        gate_source = (
            "fresh `lake build` log "
            f"({len(live)} declarations, {len(live_namespaces)} namespaces; "
            "layered over AXIOM_AUDIT.md)"
        )
    if (args.from_file is not None or args.lake) and not live:
        print("ERROR: no `#print axioms` declarations found in live build output.",
              file=sys.stderr)
        return 3
    if live:
        gates.update(live)

    guarded_types, guard_allowlist = parse_guard_configuration()
    missing_guarded = guarded_types - {entry["type"] for entry in FRONTIER}
    if missing_guarded:
        missing = ", ".join(sorted(missing_guarded))
        print(f"ERROR: guarded frontier type(s) absent from FRONTIER registry: {missing}",
              file=sys.stderr)
        return 3

    report = emit_report(
        gates,
        gate_source,
        guarded_types=guarded_types,
        guard_allowlist=guard_allowlist,
    )

    if args.stdout:
        sys.stdout.write(report)
    else:
        OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT_PATH.write_text(report, encoding="utf-8")
        print(f"Wrote {OUTPUT_PATH.relative_to(REPO_ROOT)} "
              f"({len(report.splitlines())} lines).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
