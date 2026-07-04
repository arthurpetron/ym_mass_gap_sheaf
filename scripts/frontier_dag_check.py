#!/usr/bin/env python3
"""Frontier-DAG bridge check — a static "no new orphan scorecard" guard.

## Invariant enforced

> You may NOT add a new `*Scorecard/*Frontier/*Target/*DAG` enumeration
> `structure` that carries OPEN residual atoms unless it is *bridged* to the
> unified `FrontierDAG` node (in EITHER direction — a coarsening `FrontierDAG → X`
> or a refinement `X → FrontierDAG`-inputs).

This forces open atoms to be closed by *deleting / weakening a `FrontierDAG`
field*, never by spawning a parallel scorecard that escapes accounting.  It is
the static, whole-tree companion to the build-time Lean guard
`lean/YMGapGuard.lean` (`lean-frontier-guard`): that one fails if a frontier
*type* has an unconditional inhabitant; THIS one fails if a new frontier
*enumeration* has no *bridge* relating it to `FrontierDAG`.

## Why "advisory-but-failing"

The check is grep-only Python (no `lake` needed) and mirrors the style of
`scripts/frontier_status.py` (whose parsing helpers it reuses verbatim).  On a
violation it exits non-zero AND prints exactly how a human blesses a genuine
addition, so it stops an agent from silently sharding the frontier while never
blocking a reviewed, deliberate one.

## What counts as OK for a discovered enumeration

  1. it is REGISTERED / grandfathered — its fully-qualified name is in the
     Lean guard's `frontierTypeNames`/`frontierAllowlist`, in
     `frontier_status.FRONTIER`, or in this script's reviewed `SCRIPT_ALLOWLIST`
     (the single in-script blessing surface); OR
  2. it is not an OPEN enumeration at all (no field or struct doc-block carries
     an `OPEN_MARKERS` token — an ordinary inhabited data record is exempt); OR
  3. it is BRIDGED — some `def/theorem/abbrev` in `FrontierDAG.lean` /
     `FrontierDAGBridges.lean` has a *signature* mentioning BOTH the enumeration
     and `FrontierDAG`.

Anything else is an offender.

This script edits no Lean source and proves nothing; it is a mechanical
accounting guard.  The Clay Yang–Mills mass-gap problem remains OPEN.
"""

from __future__ import annotations

import argparse
import datetime
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# Reuse the shared parsing surface from the sibling frontier-status script
# (same `scripts/` dir).  We import, never re-derive, these.
from frontier_status import (  # noqa: E402
    FRONTIER,
    LEAN_DIR,
    REPO_ROOT,
    YMGAP_PKG,
    classify,
    extract_fields,
    extract_signature,
)

# --------------------------------------------------------------------------
# Constants
# --------------------------------------------------------------------------

# A structure whose NAME signals a frontier enumeration.
ENUM_NAME_RE = re.compile(
    r"^\s*structure\s+(?P<nm>\w*(?:Scorecard|Frontier|DAG|Target)\w*)\b"
)
# The bridge target token; `FrontierDAG` lives only in FrontierDAG.lean and
# FrontierDAGBridges.lean (grep-confirmed sole occurrences).
BRIDGE_TARGET = "FrontierDAG"

GUARD_PATH = LEAN_DIR / "YMGapGuard.lean"
OUTPUT_PATH = REPO_ROOT / "docs" / "frontier-dag-check.md"

# OPEN markers used to decide whether a structure is a *frontier* enumeration
# (must be bridged) vs. an ordinary inhabited record (exempt).  We import
# `classify` from frontier_status (which consults its own OPEN_MARKERS), and we
# additionally test the struct doc-block against the same marker set.  We keep a
# local copy of the tokens only for the doc-block scan; `classify` remains the
# source of truth for per-field status.
OPEN_MARKERS = (
    "OPEN", "UNINHABITED", "NO inhabitant", "never proved", "never faked",
    "LEFT UNINHABITED", "not inhabited",
)

# --------------------------------------------------------------------------
# The single in-script reviewed blessing surface.
# --------------------------------------------------------------------------
# Fully-qualified names of enumerations that are DELIBERATELY carried as
# standalone open scorecards and have been human-reviewed as legitimate (they
# predate the unified `FrontierDAG` node and each records a genuine, distinct
# reduction).  This is the ONLY place a NEW open enumeration may be blessed
# WITHOUT a `FrontierDAG` bridge — adding here is a reviewed act, exactly like
# adding to `YMGapFrontierGuard.frontierAllowlist`.  Everything already tracked
# by the Lean guard or by `frontier_status.FRONTIER` is grandfathered
# automatically (see `registered_baseline`); this list only holds the residual
# pre-existing enumerations neither of those already covers.
SCRIPT_ALLOWLIST: set[str] = {
    "YMGap.Continuum.Tier0FrontierCorrected.Tier0FrontierC",
    "YMGap.Rubric.LoopScorecard.LoopOpenFrontier",
    "YMGap.Rubric.ContinuumScorecard.ContinuumTargetReduction",
    "YMGap.Rubric.ReconstructionScorecard.FullReconstructionTarget",
}


# --------------------------------------------------------------------------
# Data records
# --------------------------------------------------------------------------


@dataclass
class EnumInfo:
    fqname: str
    short_name: str
    module_rel: str
    struct_doc: str
    fields: list[tuple[str, str, str]] = field(default_factory=list)


@dataclass
class BridgeHit:
    decl: str
    module_rel: str
    direction: str  # "FrontierDAG->X (coarsening)" | "X->FrontierDAG (refinement)"


# --------------------------------------------------------------------------
# 1. Parse the Lean guard's tracked-name lists
# --------------------------------------------------------------------------

_BACKTICK_NAME_RE = re.compile(r"`([A-Za-z_][\w.]*)")


def _list_body(text: str, def_name: str) -> str:
    """Return the `[ ... ]` body of a `def <def_name> : List Name := [ ... ]`."""
    idx = text.find(f"def {def_name}")
    if idx < 0:
        return ""
    open_br = text.find("[", idx)
    if open_br < 0:
        return ""
    close_br = text.find("]", open_br)
    if close_br < 0:
        return ""
    return text[open_br + 1 : close_br]


def parse_guard_list() -> tuple[set[str], set[str]]:
    """Extract `(frontierTypeNames, frontierAllowlist)` backtick-qualified names
    from `lean/YMGapGuard.lean`."""
    if not GUARD_PATH.exists():
        return set(), set()
    text = GUARD_PATH.read_text(encoding="utf-8")
    guarded = set(_BACKTICK_NAME_RE.findall(_list_body(text, "frontierTypeNames")))
    allow = set(_BACKTICK_NAME_RE.findall(_list_body(text, "frontierAllowlist")))
    return guarded, allow


# --------------------------------------------------------------------------
# 2. Discover every frontier-named enumeration structure (fully qualified)
# --------------------------------------------------------------------------

_NS_RE = re.compile(r"^\s*namespace\s+(?P<ns>[\w.]+)")
_END_RE = re.compile(r"^\s*end\s+(?P<ns>[\w.]+)")


def _struct_docblock(lines: list[str], struct_line: int) -> str:
    """The `/-- ... -/` block immediately preceding the `structure` line."""
    j = struct_line - 1
    # skip blank lines directly above the structure
    while j >= 0 and lines[j].strip() == "":
        j -= 1
    if j < 0 or "-/" not in lines[j]:
        return ""
    # walk up to the opening `/--` (or `/-`), inclusive
    end = j
    start = j
    while start >= 0 and "/--" not in lines[start] and "/-" not in lines[start]:
        start -= 1
    if start < 0:
        return ""
    block = " ".join(lines[start : end + 1])
    return re.sub(r"\s+", " ", block.replace("/--", "").replace("/-", "").replace("-/", "")).strip()


def enum_infos_from_text(text: str, module_rel: str) -> list[EnumInfo]:
    """All frontier-named enumeration structures in one file, fully qualified by
    the enclosing `namespace ... end` nesting."""
    lines = text.splitlines()
    ns_stack: list[str] = []
    out: list[EnumInfo] = []
    for i, ln in enumerate(lines):
        m_ns = _NS_RE.match(ln)
        if m_ns:
            ns_stack.append(m_ns.group("ns"))
            continue
        m_end = _END_RE.match(ln)
        if m_end:
            # pop the matching namespace if present (robust to `end`/`end Foo`)
            if ns_stack and ns_stack[-1] == m_end.group("ns"):
                ns_stack.pop()
            elif ns_stack:
                ns_stack.pop()
            continue
        m_en = ENUM_NAME_RE.match(ln)
        if not m_en:
            continue
        short = m_en.group("nm")
        ns = ".".join(ns_stack)
        fqname = f"{ns}.{short}" if ns else short
        out.append(
            EnumInfo(
                fqname=fqname,
                short_name=short,
                module_rel=module_rel,
                struct_doc=_struct_docblock(lines, i),
                fields=extract_fields(text, short),
            )
        )
    return out


def discover_enumerations() -> dict[str, EnumInfo]:
    """Walk `YMGap/*.lean` (skip `.lake`) and collect every frontier-named
    enumeration keyed by fully-qualified name."""
    result: dict[str, EnumInfo] = {}
    for f in sorted(YMGAP_PKG.rglob("*.lean")):
        if "/.lake/" in str(f):
            continue
        try:
            text = f.read_text(encoding="utf-8")
        except OSError:
            continue
        rel = str(f.relative_to(LEAN_DIR))
        for info in enum_infos_from_text(text, rel):
            result[info.fqname] = info
    return result


# --------------------------------------------------------------------------
# 3. The registered / grandfathered baseline
# --------------------------------------------------------------------------


def registered_baseline(guarded: set[str], guard_allow: set[str]) -> set[str]:
    """Every enumeration already tracked somewhere reviewed: the Lean guard's
    type list + allowlist, the `frontier_status.FRONTIER` registry (types and
    their qualified sub-structs), and this script's `SCRIPT_ALLOWLIST`."""
    reg: set[str] = set(guarded) | set(guard_allow) | set(SCRIPT_ALLOWLIST)
    for e in FRONTIER:
        reg.add(e["type"])
        ns = e["type"].rsplit(".", 1)[0]
        for sub in e.get("sub_structs", []):
            reg.add(f"{ns}.{sub}")
    return reg


# --------------------------------------------------------------------------
# 4. OPEN-enumeration gate (avoid false positives on plain data records)
# --------------------------------------------------------------------------


def _has_open_marker(txt: str) -> bool:
    low = txt.lower()
    return any(m.lower() in low for m in OPEN_MARKERS)


def is_open_enumeration(info: EnumInfo) -> bool:
    """True iff any field classifies OPEN, or the struct doc-block itself carries
    an OPEN marker.  A record with no OPEN marker is ordinary data — exempt."""
    if any(st == "OPEN" for _fn, st, _doc in info.fields):
        return True
    # also re-run classify over each field doc for robustness
    if any(classify(doc) == "OPEN" for _fn, _st, doc in info.fields):
        return True
    return _has_open_marker(info.struct_doc)


# --------------------------------------------------------------------------
# 5. Bridge detection
# --------------------------------------------------------------------------

_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|theorem|abbrev)\s+"
    r"(?P<nm>[\w.']+)\b"
)
_FRONTIERDAG_BINDER_RE = re.compile(r"\(\s*\w+\s*:\s*(?:\w+\.)?FrontierDAG\b")


def _bridge_files() -> list[Path]:
    """Files whose text mentions `FrontierDAG` (cheap prefilter over the tree)."""
    out: list[Path] = []
    for f in sorted(YMGAP_PKG.rglob("*.lean")):
        if "/.lake/" in str(f):
            continue
        try:
            if BRIDGE_TARGET in f.read_text(encoding="utf-8"):
                out.append(f)
        except OSError:
            continue
    return out


def bridges_in_text(text: str, module_rel: str, candidate_short: str) -> list[BridgeHit]:
    """Every `def/theorem/abbrev` in `text` whose collapsed *signature* mentions
    BOTH `candidate_short` and `FrontierDAG`."""
    hits: list[BridgeHit] = []
    seen: set[str] = set()
    for ln in text.splitlines():
        m = _DECL_RE.match(ln)
        if not m:
            continue
        decl_short = m.group("nm").split(".")[-1]
        if decl_short in seen:
            continue
        seen.add(decl_short)
        sig = extract_signature(text, decl_short)
        if candidate_short in sig and BRIDGE_TARGET in sig:
            # direction: FrontierDAG in a binder => coarsening FrontierDAG -> X;
            # otherwise (conclusion) => refinement X -> FrontierDAG-inputs.
            if _FRONTIERDAG_BINDER_RE.search(sig):
                direction = "FrontierDAG->X (coarsening)"
            else:
                direction = "X->FrontierDAG (refinement)"
            hits.append(BridgeHit(decl=decl_short, module_rel=module_rel, direction=direction))
    return hits


def find_bridge(candidate_short: str, files: list[Path]) -> list[BridgeHit]:
    hits: list[BridgeHit] = []
    for f in files:
        try:
            text = f.read_text(encoding="utf-8")
        except OSError:
            continue
        hits.extend(bridges_in_text(text, str(f.relative_to(LEAN_DIR)), candidate_short))
    return hits


# --------------------------------------------------------------------------
# 6. Offender loop + report
# --------------------------------------------------------------------------


@dataclass
class CheckResult:
    total: int
    registered: list[str]
    bridged: list[tuple[str, list[BridgeHit]]]
    exempt: list[str]  # not an OPEN enumeration
    offenders: list[EnumInfo]


def run_check() -> CheckResult:
    guarded, guard_allow = parse_guard_list()
    registered = registered_baseline(guarded, guard_allow)
    enums = discover_enumerations()
    bridge_files = _bridge_files()

    reg_hits: list[str] = []
    exempt: list[str] = []
    bridged: list[tuple[str, list[BridgeHit]]] = []
    offenders: list[EnumInfo] = []

    for info in enums.values():
        if info.fqname in registered:
            reg_hits.append(info.fqname)
            continue
        if not is_open_enumeration(info):
            exempt.append(info.fqname)
            continue
        hits = find_bridge(info.short_name, bridge_files)
        if hits:
            bridged.append((info.fqname, hits))
            continue
        offenders.append(info)

    return CheckResult(
        total=len(enums),
        registered=reg_hits,
        bridged=bridged,
        exempt=exempt,
        offenders=offenders,
    )


REMEDY = (
    "either (a) add a `FrontierDAG`<->bridge decl a la `toSubWallA` "
    "(`FrontierDAG.lean`) or `frontierTrueMargin_qFloor` "
    "(`FrontierDAGBridges.lean`) whose SIGNATURE mentions BOTH the enumeration "
    "and `FrontierDAG`; or (b) bless it (reviewed) in "
    "`frontier_status.FRONTIER`, `YMGapFrontierGuard.frontierAllowlist`, or "
    "`frontier_dag_check.SCRIPT_ALLOWLIST`."
)


def emit_report(res: CheckResult) -> str:
    today = datetime.date.today().isoformat()
    L: list[str] = []
    A = L.append
    A("# Frontier-DAG bridge check")
    A("")
    A(f"> **Auto-generated** by `scripts/frontier_dag_check.py` on {today}.")
    A("> Static accounting guard — edits no Lean source. Enforces: no NEW open")
    A("> `*Scorecard/*Frontier/*Target/*DAG` enumeration without a `FrontierDAG`")
    A("> bridge. The Clay Yang-Mills mass-gap problem remains OPEN.")
    A("")
    A("## Summary")
    A("")
    A(f"- enumerations discovered: **{res.total}**")
    A(f"- registered / grandfathered: **{len(res.registered)}**")
    A(f"- bridged to `FrontierDAG`: **{len(res.bridged)}**")
    A(f"- exempt (not an OPEN enumeration): **{len(res.exempt)}**")
    A(f"- **UNBRIDGED offenders: {len(res.offenders)}**")
    A("")
    if res.bridged:
        A("## Bridged enumerations")
        A("")
        for fq, hits in sorted(res.bridged):
            hs = ", ".join(f"`{h.decl}` [{h.direction}]" for h in hits)
            A(f"- `{fq}` -- {hs}")
        A("")
    if res.offenders:
        A("## OFFENDERS (unbridged, unregistered OPEN enumerations)")
        A("")
        for info in res.offenders:
            A(f"- `{info.fqname}` (`lean/{info.module_rel}`) -- "
              f"no def/theorem/abbrev relates it to `FrontierDAG`.")
            A(f"  Remedy: {REMEDY}")
        A("")
    else:
        A("No offenders: every new open enumeration is bridged or blessed.")
        A("")
    return "\n".join(L) + "\n"


# --------------------------------------------------------------------------
# Self-test (exercises bridge + offender detection on synthetic text)
# --------------------------------------------------------------------------


def _self_test() -> int:
    ok = True

    def check(name: str, cond: bool) -> None:
        nonlocal ok
        status = "ok  " if cond else "FAIL"
        print(f"  [{status}] {name}")
        if not cond:
            ok = False

    # (a) discovery + namespace qualification
    sample = (
        "namespace YMGap.Demo\n"
        "/-- DELIBERATELY UNINHABITED demo. -/\n"
        "structure DemoScorecard : Type where\n"
        "  /-- OPEN atom. -/\n"
        "  atom : Foo\n"
        "end YMGap.Demo\n"
    )
    infos = enum_infos_from_text(sample, "Demo.lean")
    check("discovers namespaced enum", len(infos) == 1
          and infos[0].fqname == "YMGap.Demo.DemoScorecard")
    check("open-enumeration gate fires on OPEN field/doc",
          is_open_enumeration(infos[0]))

    # (b) plain (non-open) record is exempt
    plain = (
        "namespace YMGap.Demo\n"
        "/-- Inhabited data record. -/\n"
        "structure PlainTarget : Type where\n"
        "  /-- the value. -/\n"
        "  v : Nat\n"
        "end YMGap.Demo\n"
    )
    p_infos = enum_infos_from_text(plain, "Plain.lean")
    check("plain record discovered", len(p_infos) == 1)
    check("plain record is exempt (not OPEN)",
          not is_open_enumeration(p_infos[0]))

    # (c) coarsening bridge FrontierDAG -> X detected in a binder
    coarse = (
        "def toDemo (F : FrontierDAG p w) : DemoScorecard where\n"
        "  atom := F.atom\n"
    )
    hits = bridges_in_text(coarse, "Bridge.lean", "DemoScorecard")
    check("coarsening bridge detected", len(hits) == 1
          and hits[0].direction == "FrontierDAG->X (coarsening)")

    # (d) refinement bridge X -> FrontierDAG detected in conclusion
    refine = (
        "def ofDemo (d : DemoScorecard) : FrontierDAG p w :=\n"
        "  sorry\n"
    )
    hits2 = bridges_in_text(refine, "Bridge.lean", "DemoScorecard")
    check("refinement bridge detected", len(hits2) == 1
          and hits2[0].direction == "X->FrontierDAG (refinement)")

    # (e) body-only mention is NOT a bridge (signature stops at :=)
    bodyonly = (
        "def unrelated (d : DemoScorecard) : Nat :=\n"
        "  FrontierDAG.size d\n"
    )
    check("body-only FrontierDAG mention is not a bridge",
          bridges_in_text(bodyonly, "B.lean", "DemoScorecard") == [])

    # (f) live tree: the real check exits clean
    res = run_check()
    check("live tree has zero offenders", not res.offenders)
    check("live tree discovers the 9 known enumerations", res.total >= 9)

    print(f"\nself-test: {'PASS' if ok else 'FAIL'}")
    return 0 if ok else 1


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Fail if a new *Scorecard/*Frontier/*Target/*DAG enumeration "
                    "lacks a FrontierDAG bridge."
    )
    ap.add_argument("--write", action="store_true",
                    help="Also write docs/frontier-dag-check.md (opt-in; default is stdout-only).")
    ap.add_argument("--self-test", action="store_true",
                    help="Run the built-in synthetic detection tests and exit.")
    args = ap.parse_args()

    if args.self_test:
        return _self_test()

    res = run_check()
    report = emit_report(res)

    if args.write:
        OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT_PATH.write_text(report, encoding="utf-8")
        print(f"Wrote {OUTPUT_PATH.relative_to(REPO_ROOT)} "
              f"({len(report.splitlines())} lines).")

    if res.offenders:
        print("frontier-dag-check FAILED: "
              f"{len(res.offenders)} unbridged open enumeration(s).",
              file=sys.stderr)
        for info in res.offenders:
            print(f"  - {info.fqname} (lean/{info.module_rel}): "
                  "no def/theorem/abbrev relates it to FrontierDAG.",
                  file=sys.stderr)
        print(f"\nRemedy: {REMEDY}", file=sys.stderr)
        return 2

    print(
        f"frontier-dag-check OK: {res.total} enumerations, "
        f"{len(res.registered)} registered/grandfathered, "
        f"{len(res.bridged)} bridged, "
        f"{len(res.exempt)} exempt, 0 unbridged."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
