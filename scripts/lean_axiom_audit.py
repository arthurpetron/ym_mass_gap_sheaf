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
    per namespace, a hash of that namespace's sorted `name = axioms` map.

CI stays fast, diffs are reviewable (a changed namespace touches one hash
line), and regeneration is per-namespace rather than whole-file.

# Usage

    python scripts/lean_axiom_audit.py            # check vs baseline
    python scripts/lean_axiom_audit.py --update   # regenerate baseline
    python scripts/lean_axiom_audit.py --strict   # also fail on namespace-digest drift

Exit codes:
  0  -- clean (gate held; --strict: no digest drift).
  1  -- GATE FAIL: a theorem depends on an axiom outside the gate and is not
        a reviewed EXCEPTION (proof became non-constructive).
  2  -- (--strict) namespace-digest drift: some namespace's axiom profile
        changed (new/removed decls, or within-gate axiom changes).
  3  -- infrastructure error (build failed, no axiom info, missing baseline).

# Semantics

  * DEFAULT (`--`): the GATE check.  Fails only if a theorem depends on an
    axiom `∉ {propext, Quot.sound}` that is not in EXCEPTIONS.  Within-gate
    changes, new theorems, and shrinks pass silently (they respect the gate).
    This matches AGENTS.md Rule 1 exactly.
  * STRICT (`--strict`): additionally the DIGEST check.  Fails if any
    namespace's digest differs from the baseline (any axiom-profile change).
    Use for deliberate review; regenerate with `--update`.

# Companion files / integration

  * `lean/AXIOM_AUDIT.md`         -- the hashed baseline (this script writes it).
  * `lean/AGENTS.md`             -- the constructivity contract Rule 1 enforces.
  * `scripts/frontier_status.py` -- reads the EXCEPTIONS list; clean decls default.
  * `make lean-audit[-strict|-update]`, `.github/workflows/lean-audit.yml`.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO_ROOT / "lean"
BASELINE_PATH = LEAN_DIR / "AXIOM_AUDIT.md"

# The permitted axiom gate (AGENTS.md Rule 1). Anything else => EXCEPTIONS.
GATE = frozenset({"propext", "Quot.sound"})

# --------------------------------------------------------------------------
# Lake-output parsing (unchanged shape — shared with frontier_status.py)
# --------------------------------------------------------------------------

THEOREM_PATTERN = re.compile(
    r"'(?P<name>YMGap[\w\\.']+?)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)"
)


def parse_lake_output(output: str) -> dict[str, set[str]]:
    """Parse `lake build` output; return {theorem_name: set_of_axioms}."""
    result: dict[str, set[str]] = {}
    # Lean's formatter may wrap a long `#print axioms` declaration between
    # comma-separated axioms, for example `[propext,\n Quot.sound]`.  Search
    # the complete output instead of one physical line at a time so those
    # load-bearing declarations are not silently omitted from the audit.
    for m in THEOREM_PATTERN.finditer(output):
        name = m.group("name")
        axioms_str = m.group("axioms")
        if axioms_str is None:
            result[name] = set()
        else:
            result[name] = {a.strip() for a in axioms_str.split(",") if a.strip()}
    return result


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
    return {n: ax for n, ax in observed.items() if not ax <= GATE}


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
per-namespace hash of the full `name = axioms` map, so drift is detected and
regeneration is per-namespace (a one-line diff), not whole-file.

## Policy

  * **GATE FAIL** (`make lean-audit`): a theorem depends on an axiom outside
    `{propext, Quot.sound}` and is not listed under `## Exceptions`.
  * **DIGEST DRIFT** (`make lean-audit-strict`): a namespace's digest differs
    from the recorded value (any axiom-profile change — new/removed decls or
    within-gate axiom shifts).  Review, then `make lean-audit-update`.

## Format

```
## Exceptions
<fully-qualified-name> = <comma-separated axioms outside the gate>   [# note]

## Namespace digests
<namespace> = <sha16>  (<decl-count>)
```

Lines starting with `#`/`>` and blanks are ignored.
"""

_EXC_RE = re.compile(r"^(?P<name>YMGap[\w\\.']+?)\s*=\s*(?P<axioms>.*?)\s*(?:#.*)?$")
_DIG_RE = re.compile(
    r"^(?P<ns>YMGap[\w\\.']*?)\s*=\s*(?P<hash>[0-9a-f]{8,64})\s*(?:\(\s*(?P<count>\d+)\s*\))?\s*$"
)


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
    """Return (exceptions, digests) from the hashed baseline.

    Backward-compatible: an OLD flat `name = axioms` baseline is read as
    exceptions being every non-gate line; digests come back empty (strict mode
    is then a no-op until the first `--update`).
    """
    exc: dict[str, set[str]] = {}
    digests: dict[str, tuple[str, int]] = {}
    if not path.exists():
        return exc, digests
    section = None
    for line in path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if s.startswith("## Exceptions"):
            section = "exc"
            continue
        if s.startswith("## Namespace digests"):
            section = "dig"
            continue
        if not s or s.startswith("#") or s.startswith(">"):
            continue
        if section == "dig":
            m = _DIG_RE.match(s)
            if m:
                digests[m.group("ns")] = (
                    m.group("hash"),
                    int(m.group("count") or 0),
                )
            continue
        # section == "exc" (or an old flat baseline with no section headers)
        m = _EXC_RE.match(s)
        if m and m.group("name").startswith("YMGap"):
            axset = {a.strip() for a in m.group("axioms").split(",") if a.strip()}
            # In an OLD flat baseline, keep only genuine non-gate lines as exceptions.
            if not axset <= GATE:
                exc[m.group("name")] = axset
    return exc, digests


# --------------------------------------------------------------------------
# Build invocation
# --------------------------------------------------------------------------


def run_lake_build() -> tuple[int, str]:
    proc = subprocess.run(
        ["lake", "build"], cwd=LEAN_DIR, capture_output=True, text=True, check=False
    )
    return proc.returncode, proc.stdout + proc.stderr


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
    args = parser.parse_args()

    if args.from_file is not None:
        if not args.from_file.exists():
            print(f"ERROR: --from-file path does not exist: {args.from_file}", file=sys.stderr)
            return 3
        output = args.from_file.read_text(encoding="utf-8")
    else:
        rc, output = run_lake_build()
        if rc != 0:
            print(f"ERROR: lake build failed (exit {rc}).", file=sys.stderr)
            print(output, file=sys.stderr)
            return 3

    observed = parse_lake_output(output)
    if not observed:
        print("ERROR: no `#print axioms` info found in lake-build output.", file=sys.stderr)
        return 3

    if args.update:
        write_baseline(BASELINE_PATH, observed)
        exc = exceptions_of(observed)
        digs = compute_digests(observed)
        print(f"Baseline updated: {len(observed)} theorems, {len(digs)} namespaces, "
              f"{len(exc)} exception(s) -> {BASELINE_PATH.relative_to(REPO_ROOT)}")
        return 0

    base_exc, base_dig = parse_baseline(BASELINE_PATH)
    if not base_exc and not base_dig:
        print(f"ERROR: baseline {BASELINE_PATH.relative_to(REPO_ROOT)} missing/empty. "
              f"Run `make lean-audit-update` first.", file=sys.stderr)
        return 3

    obs_exc = exceptions_of(observed)
    # GATE check: any theorem outside the gate must be a reviewed exception with
    # a superset-permitted record.
    gate_fails: list[str] = []
    for name, ax in obs_exc.items():
        permitted = base_exc.get(name)
        if permitted is None or not ax <= permitted:
            extra = ax - (permitted or set())
            gate_fails.append(
                f"  - {name}: axioms {{{', '.join(sorted(ax))}}} outside gate "
                f"{{propext, Quot.sound}}; unreviewed {{{', '.join(sorted(extra))}}}"
            )

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
            elif o[0] != b[0]:
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
