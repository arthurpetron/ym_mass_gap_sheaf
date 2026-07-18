#!/usr/bin/env python3
"""Static Lean import/coverage guard and affected-target planner.

This script never invokes Lean or Lake.  It checks four source-level invariants:

* every local ``YMGap...`` import names an existing source module;
* the active Lake configuration keeps the expected source root, default
  targets, Lean-artifact facets, and ``YMGap.*`` glob, so a bare full build
  really compiles every source module and both audit guards;
* every module is reachable from the semantic root ``lean/YMGap.lean`` or from
  a reviewed alternative root in ``lean/SEMANTIC_ROOT_EXCLUSIONS.txt``;
* reviewed alternative roots are present, genuinely outside the main closure,
  non-redundant, and documented with a reason.

``--affected [BASE]`` adds a read-only Git analysis.  It reports maximal
transitive reverse-dependent module targets for changed tracked and untracked
Lean files.  Edges from the three flat aggregator modules (``YMGap``,
``YMGapGuard``, and ``YMGapStatementGuard``) are deliberately omitted from the
reverse graph; otherwise every ordinary edit would misleadingly plan a full
root build.  A Lake configuration or toolchain change is reported separately as
requiring a full build.

Exit codes:

* 0: all static checks passed;
* 1: import, coverage, or semantic-root classification failed;
* 2: ``--affected`` found a configuration/toolchain change requiring a full
  build (the static checks may still have passed);
* 3: infrastructure failure, such as an unreadable Git diff.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path, PurePosixPath


REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO_ROOT / "lean"
PACKAGE_DIR = LEAN_DIR / "YMGap"
SEMANTIC_ROOT_PATH = LEAN_DIR / "YMGap.lean"
LAKEFILE_PATH = LEAN_DIR / "lakefile.toml"
EXCLUSIONS_PATH = LEAN_DIR / "SEMANTIC_ROOT_EXCLUSIONS.txt"

AGGREGATOR_PATHS = {
    "YMGap": SEMANTIC_ROOT_PATH,
    "YMGapGuard": LEAN_DIR / "YMGapGuard.lean",
    "YMGapStatementGuard": LEAN_DIR / "YMGapStatementGuard.lean",
}
IGNORED_REVERSE_IMPORTERS = frozenset(AGGREGATOR_PATHS)
REQUIRED_DEFAULT_TARGETS = (
    "YMGap",
    "YMGapGuard",
    "YMGapStatementGuard",
)

FULL_BUILD_PATHS = frozenset(
    {
        ".github/workflows/lean-audit.yml",
        "Makefile",
        "lean/lakefile.toml",
        "lean/lakefile.lean",
        "lean/lake-manifest.json",
        "lean/lean-toolchain",
        "scripts/lean_import_guard.py",
    }
)

SOURCE_COMPONENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
MODULE_RE = re.compile(r"^YMGap(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
LOCAL_MODULE_PATTERN = (
    r"(?:YMGap(?:\.[A-Za-z_][A-Za-z0-9_']*)*|"
    r"YMGapGuard(?:\.[A-Za-z_][A-Za-z0-9_']*)*|"
    r"YMGapStatementGuard(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
)
IMPORT_RE = re.compile(
    r"(?<![.\w'])import\s+(?:all\s+)?"
    rf"(?P<module>{LOCAL_MODULE_PATTERN})(?![.\w'])"
)


@dataclass(frozen=True)
class ImportProblem:
    importer: str
    imported: str
    source: Path


@dataclass(frozen=True)
class ExclusionReport:
    classified: frozenset[str]
    missing_roots: tuple[str, ...]
    non_orphan_roots: tuple[str, ...]
    stale_roots: tuple[str, ...]


@dataclass(frozen=True)
class LakeCoverage:
    globs: tuple[str, ...]
    default_targets: tuple[str, ...]


@dataclass(frozen=True)
class Analysis:
    main_sources: dict[str, Path]
    graph_sources: dict[str, Path]
    graph: dict[str, set[str]]
    import_count: int
    missing_imports: tuple[ImportProblem, ...]
    import_cycles: tuple[tuple[str, ...], ...]
    semantic_closure: frozenset[str]
    semantic_orphans: frozenset[str]
    exclusions: dict[str, str]
    exclusion_report: ExclusionReport
    unexpected_orphans: frozenset[str]
    globs: tuple[str, ...]
    default_targets: tuple[str, ...]
    uncovered_modules: tuple[str, ...]
    issues: tuple[str, ...]


def executable_text(source: str) -> str:
    """Remove nested Lean comments and strings while preserving line breaks."""
    output: list[str] = []
    index = 0
    comment_depth = 0
    in_string = False
    escaped = False

    while index < len(source):
        if comment_depth:
            if source.startswith("/-", index):
                comment_depth += 1
                index += 2
            elif source.startswith("-/", index):
                comment_depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    output.append("\n")
                index += 1
        elif in_string:
            char = source[index]
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            if char == "\n":
                output.append("\n")
            index += 1
        elif source.startswith("/-", index):
            comment_depth = 1
            index += 2
        elif source.startswith("--", index):
            newline = source.find("\n", index)
            if newline < 0:
                break
            output.append("\n")
            index = newline + 1
        elif source[index] == '"':
            in_string = True
            index += 1
        else:
            output.append(source[index])
            index += 1

    return "".join(output)


def file_to_module(path: Path, lean_dir: Path = LEAN_DIR) -> str:
    """Convert a Lean source path under ``lean/`` to its module name."""
    relative = path.relative_to(lean_dir).with_suffix("")
    return ".".join(relative.parts)


def repo_path_to_module(path: str) -> str | None:
    """Convert a repository-relative ``lean/**/*.lean`` path to a module."""
    pure = PurePosixPath(path)
    if len(pure.parts) < 2 or pure.parts[0] != "lean" or pure.suffix != ".lean":
        return None
    return ".".join(pure.with_suffix("").parts[1:])


def discover_main_sources(
    package_dir: Path = PACKAGE_DIR,
    semantic_root_path: Path = SEMANTIC_ROOT_PATH,
) -> tuple[dict[str, Path], list[str]]:
    """Enumerate ``YMGap.lean`` and every ``YMGap/**/*.lean`` source."""
    issues: list[str] = []
    sources: dict[str, Path] = {}
    candidates = [semantic_root_path]
    if package_dir.exists():
        candidates.extend(sorted(package_dir.rglob("*.lean")))

    for path in candidates:
        if not path.exists():
            issues.append(f"missing required Lean source: {path.relative_to(REPO_ROOT)}")
            continue
        relative_module_path = path.relative_to(semantic_root_path.parent).with_suffix("")
        invalid_components = tuple(
            component
            for component in relative_module_path.parts
            if not SOURCE_COMPONENT_RE.fullmatch(component)
        )
        if invalid_components:
            issues.append(
                f"invalid Lean module path {path.relative_to(REPO_ROOT)}: "
                f"unsupported component(s) {', '.join(repr(item) for item in invalid_components)}"
            )
            continue
        module = file_to_module(path, semantic_root_path.parent)
        previous = sources.get(module)
        if previous is not None and previous != path:
            issues.append(
                f"duplicate module {module}: {previous.relative_to(REPO_ROOT)} and "
                f"{path.relative_to(REPO_ROOT)}"
            )
            continue
        sources[module] = path
    return sources, issues


def discover_graph_sources(
    main_sources: dict[str, Path],
    aggregator_paths: dict[str, Path] = AGGREGATOR_PATHS,
) -> tuple[dict[str, Path], list[str]]:
    """Add the two guard roots to the graph used by ``--affected``."""
    sources = dict(main_sources)
    issues: list[str] = []
    for module, path in aggregator_paths.items():
        if module == "YMGap":
            continue
        if not path.exists():
            issues.append(f"missing aggregator source: {path.relative_to(REPO_ROOT)}")
            continue
        sources[module] = path
    return sources, issues


def parse_local_imports(source: str) -> set[str]:
    """Return lexical local imports, including module-system import variants."""
    clean = executable_text(source)
    return {match.group("module") for match in IMPORT_RE.finditer(clean)}


def build_import_graph(
    sources: dict[str, Path],
) -> tuple[dict[str, set[str]], int, tuple[ImportProblem, ...]]:
    """Build importer-to-imports edges and report unresolved local imports."""
    graph: dict[str, set[str]] = {}
    import_count = 0
    problems: list[ImportProblem] = []
    for module, path in sorted(sources.items()):
        imports = parse_local_imports(path.read_text(encoding="utf-8", errors="replace"))
        graph[module] = imports
        import_count += len(imports)
        for imported in sorted(imports):
            if imported not in sources:
                problems.append(ImportProblem(module, imported, path))
    return graph, import_count, tuple(problems)


def dependency_closure(graph: dict[str, set[str]], roots: set[str]) -> set[str]:
    """Return the transitive local-import closure of ``roots`` (including roots)."""
    visited: set[str] = set()
    work = sorted(roots, reverse=True)
    while work:
        module = work.pop()
        if module in visited:
            continue
        visited.add(module)
        work.extend(dep for dep in graph.get(module, set()) if dep not in visited)
    return visited


def find_import_cycles(graph: dict[str, set[str]]) -> tuple[tuple[str, ...], ...]:
    """Return canonical witnesses for local-import cycles, without recursion."""
    color: dict[str, int] = {module: 0 for module in graph}  # 0 white, 1 gray, 2 black
    witnesses: set[tuple[str, ...]] = set()

    for start in sorted(graph):
        if color[start] != 0:
            continue
        color[start] = 1
        stack: list[tuple[str, Iterator[str]]] = [
            (start, iter(sorted(dep for dep in graph[start] if dep in graph)))
        ]
        positions: dict[str, int] = {start: 0}
        while stack:
            module, iterator = stack[-1]
            try:
                dependency = next(iterator)
            except StopIteration:
                color[module] = 2
                positions.pop(module, None)
                stack.pop()
                continue

            if color[dependency] == 0:
                color[dependency] = 1
                positions[dependency] = len(stack)
                stack.append(
                    (
                        dependency,
                        iter(sorted(dep for dep in graph[dependency] if dep in graph)),
                    )
                )
            elif color[dependency] == 1:
                first = positions[dependency]
                cycle = tuple(item[0] for item in stack[first:])
                rotations = [cycle[index:] + cycle[:index] for index in range(len(cycle))]
                witnesses.add(min(rotations))

    return tuple(sorted(witnesses))


def parse_exclusion_manifest(text: str) -> tuple[dict[str, str], list[str]]:
    """Parse ``Module.Name # nonempty reason`` semantic-root exclusions."""
    exclusions: dict[str, str] = {}
    issues: list[str] = []
    for line_number, raw_line in enumerate(text.splitlines(), 1):
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if "#" not in raw_line:
            issues.append(
                f"semantic exclusion line {line_number}: expected 'Module.Name # reason'"
            )
            continue
        module_text, reason_text = raw_line.split("#", 1)
        module = module_text.strip()
        reason = reason_text.strip()
        if not MODULE_RE.fullmatch(module):
            issues.append(
                f"semantic exclusion line {line_number}: invalid YMGap module {module!r}"
            )
            continue
        if not reason:
            issues.append(
                f"semantic exclusion line {line_number}: {module} has no review reason"
            )
            continue
        if module in exclusions:
            issues.append(
                f"semantic exclusion line {line_number}: duplicate root {module}"
            )
            continue
        exclusions[module] = reason
    return exclusions, issues


def load_exclusion_manifest(path: Path = EXCLUSIONS_PATH) -> tuple[dict[str, str], list[str]]:
    if not path.exists():
        return {}, [f"missing semantic-root exclusion manifest: {path.relative_to(REPO_ROOT)}"]
    return parse_exclusion_manifest(path.read_text(encoding="utf-8"))


def classify_exclusions(
    modules: set[str],
    graph: dict[str, set[str]],
    semantic_closure: set[str],
    exclusions: dict[str, str],
) -> ExclusionReport:
    """Classify orphan closures and reject missing, non-orphan, or redundant roots."""
    missing = tuple(sorted(root for root in exclusions if root not in modules))
    non_orphan = tuple(sorted(root for root in exclusions if root in semantic_closure))

    valid_roots = set(exclusions) - set(missing) - set(non_orphan)
    closures = {root: dependency_closure(graph, {root}) for root in valid_roots}
    stale: list[str] = []
    for root in sorted(valid_roots):
        covered_by_others: set[str] = set()
        for other_root, other_closure in closures.items():
            if other_root != root:
                covered_by_others.update(other_closure)
        if root in covered_by_others:
            stale.append(root)

    classified: set[str] = set()
    for root, closure in closures.items():
        if root not in stale:
            classified.update((closure & modules) - semantic_closure)
    return ExclusionReport(
        classified=frozenset(classified),
        missing_roots=missing,
        non_orphan_roots=non_orphan,
        stale_roots=tuple(stale),
    )


def glob_matches(pattern: str, module: str) -> bool:
    """Match Lake's ``Name``, ``Name.+``, and ``Name.*`` TOML glob forms."""
    if pattern.endswith(".*"):
        root = pattern[:-2]
        return module == root or module.startswith(root + ".")
    if pattern.endswith(".+"):
        root = pattern[:-2]
        return module.startswith(root + ".")
    return module == pattern


def decode_string_sequence(
    value: object, label: str, *, allow_singleton: bool = True
) -> tuple[tuple[str, ...], list[str]]:
    """Decode a Lake string array (and fields that accept a singleton string)."""
    if allow_singleton and isinstance(value, str):
        return (value,), []
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return tuple(value), []
    expected = "a string or an array of strings" if allow_singleton else "an array of strings"
    return (), [f"{label} must be {expected}"]


def is_current_directory(value: object) -> bool:
    """Recognize lexical spellings of Lake's default current-directory srcDir."""
    return isinstance(value, str) and PurePosixPath(value) == PurePosixPath(".")


def lake_coverage_from_data(data: dict[str, object]) -> tuple[LakeCoverage, list[str]]:
    """Validate the Lake settings on which the repository build contract relies."""
    issues: list[str] = []

    default_targets, target_issues = decode_string_sequence(
        data.get("defaultTargets", []), "Lake defaultTargets", allow_singleton=False
    )
    issues.extend(target_issues)
    missing_targets = tuple(
        target for target in REQUIRED_DEFAULT_TARGETS if target not in default_targets
    )
    if missing_targets:
        issues.append(
            "Lake defaultTargets must include the production library and both audit guards; "
            f"missing {', '.join(missing_targets)}"
        )

    package_src_dir = data.get("srcDir", ".")
    if not is_current_directory(package_src_dir):
        issues.append(
            "Lake package srcDir must remain '.' because the import guard enumerates lean/"
        )

    raw_libraries = data.get("lean_lib", [])
    if isinstance(raw_libraries, list):
        libraries = raw_libraries
    elif isinstance(raw_libraries, dict):
        libraries = [raw_libraries]
    else:
        libraries = []
        issues.append("Lake lean_lib configuration must be an array of tables")

    main_globs: tuple[str, ...] = ()
    for target in REQUIRED_DEFAULT_TARGETS:
        matching = [
            library
            for library in libraries
            if isinstance(library, dict) and library.get("name") == target
        ]
        if len(matching) != 1:
            issues.append(
                f"expected exactly one [[lean_lib]] with name = {target!r}; "
                f"found {len(matching)}"
            )
            continue

        library = matching[0]
        if not is_current_directory(library.get("srcDir", ".")):
            issues.append(
                f"{target} lean_lib srcDir must remain '.' because the import guard "
                "enumerates lean/"
            )

        roots, root_issues = decode_string_sequence(
            library.get("roots", [target]), f"{target} lean_lib roots"
        )
        issues.extend(root_issues)
        globs, glob_issues = decode_string_sequence(
            library.get("globs", list(roots)), f"{target} lean_lib globs"
        )
        issues.extend(glob_issues)

        default_facets, facet_issues = decode_string_sequence(
            library.get("defaultFacets", ["leanArts"]),
            f"{target} lean_lib defaultFacets",
        )
        issues.extend(facet_issues)
        if "leanArts" not in default_facets:
            issues.append(
                f"{target} lean_lib defaultFacets must include 'leanArts' so a bare "
                "library build compiles Lean artifacts"
            )

        if target == "YMGap":
            main_globs = globs
            if "YMGap.*" not in globs:
                issues.append(
                    "YMGap lean_lib must explicitly include globs = [\"YMGap.*\"] so "
                    "every YMGap module is compiled independently"
                )
        elif not any(glob_matches(pattern, target) for pattern in globs):
            issues.append(
                f"{target} lean_lib globs/roots do not select the {target} audit module"
            )

    return LakeCoverage(main_globs, default_targets), issues


def load_lake_coverage(path: Path = LAKEFILE_PATH) -> tuple[LakeCoverage, list[str]]:
    """Load TOML and reject a higher-precedence ``lakefile.lean`` override."""
    issues: list[str] = []
    lean_override = path.with_suffix(".lean")
    if lean_override.exists():
        issues.append(
            f"{lean_override.relative_to(REPO_ROOT)} overrides lakefile.toml; "
            "the import guard cannot verify a Lean-DSL Lake configuration"
        )
    if not path.exists():
        issues.append(f"missing Lake configuration: {path.relative_to(REPO_ROOT)}")
        return LakeCoverage((), ()), issues
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except tomllib.TOMLDecodeError as exc:
        issues.append(f"invalid {path.relative_to(REPO_ROOT)}: {exc}")
        return LakeCoverage((), ()), issues

    coverage, coverage_issues = lake_coverage_from_data(data)
    issues.extend(coverage_issues)
    return coverage, issues


def analyze_repository() -> Analysis:
    issues: list[str] = []
    main_sources, discovery_issues = discover_main_sources()
    issues.extend(discovery_issues)
    graph_sources, aggregator_issues = discover_graph_sources(main_sources)
    issues.extend(aggregator_issues)

    graph, import_count, missing_imports = build_import_graph(graph_sources)
    for problem in missing_imports:
        issues.append(
            f"unresolved local import {problem.imported} in "
            f"{problem.source.relative_to(REPO_ROOT)} ({problem.importer})"
        )
    import_cycles = find_import_cycles(graph)
    for cycle in import_cycles:
        issues.append(f"cyclic local import: {' -> '.join((*cycle, cycle[0]))}")

    semantic_closure = dependency_closure(graph, {"YMGap"}) & set(main_sources)
    semantic_orphans = set(main_sources) - semantic_closure

    exclusions, manifest_issues = load_exclusion_manifest()
    issues.extend(manifest_issues)
    exclusion_report = classify_exclusions(
        set(main_sources), graph, semantic_closure, exclusions
    )
    for root in exclusion_report.missing_roots:
        issues.append(f"semantic exclusion root does not exist: {root}")
    for root in exclusion_report.non_orphan_roots:
        issues.append(f"semantic exclusion root is already reachable from YMGap: {root}")
    for root in exclusion_report.stale_roots:
        issues.append(f"semantic exclusion root is redundant/stale: {root}")

    unexpected_orphans = semantic_orphans - set(exclusion_report.classified)
    if unexpected_orphans:
        issues.append(
            f"{len(unexpected_orphans)} semantic orphan(s) lack a reviewed exclusion root"
        )

    lake_coverage, lake_issues = load_lake_coverage()
    issues.extend(lake_issues)
    globs = lake_coverage.globs
    uncovered = tuple(
        sorted(
            module
            for module in main_sources
            if not any(glob_matches(pattern, module) for pattern in globs)
        )
    )
    if uncovered:
        issues.append(f"{len(uncovered)} module(s) are not selected by YMGap lean_lib globs")

    return Analysis(
        main_sources=main_sources,
        graph_sources=graph_sources,
        graph=graph,
        import_count=import_count,
        missing_imports=missing_imports,
        import_cycles=import_cycles,
        semantic_closure=frozenset(semantic_closure),
        semantic_orphans=frozenset(semantic_orphans),
        exclusions=exclusions,
        exclusion_report=exclusion_report,
        unexpected_orphans=frozenset(unexpected_orphans),
        globs=globs,
        default_targets=lake_coverage.default_targets,
        uncovered_modules=uncovered,
        issues=tuple(issues),
    )


def print_analysis(analysis: Analysis) -> None:
    print("lean-import-guard")
    print(f"  source modules:       {len(analysis.main_sources)}")
    print(f"  local import edges:   {analysis.import_count}")
    print(f"  local import cycles:  {len(analysis.import_cycles)}")
    print(f"  semantic-root reach:  {len(analysis.semantic_closure)}")
    print(f"  semantic orphans:     {len(analysis.semantic_orphans)}")
    print(f"  classified orphans:   {len(analysis.exclusion_report.classified)}")
    print(f"  unexpected orphans:   {len(analysis.unexpected_orphans)}")
    print(f"  YMGap library globs:   {', '.join(analysis.globs) if analysis.globs else '(none)'}")
    print(
        "  Lake default targets: "
        f"{', '.join(analysis.default_targets) if analysis.default_targets else '(none)'}"
    )

    if analysis.exclusions:
        print("reviewed semantic-root exclusions:")
        for module, reason in sorted(analysis.exclusions.items()):
            print(f"  - {module}: {reason}")

    if analysis.unexpected_orphans:
        print("unexpected semantic orphans:")
        for module in sorted(analysis.unexpected_orphans):
            print(f"  - {module}")

    if analysis.uncovered_modules:
        print("modules not selected by the YMGap lean_lib globs:")
        for module in analysis.uncovered_modules:
            print(f"  - {module}")

    if analysis.issues:
        print("lean-import-guard FAILED:", file=sys.stderr)
        for issue in analysis.issues:
            print(f"  - {issue}", file=sys.stderr)
    else:
        print("lean-import-guard: PASS")


def decode_nul_paths(output: bytes) -> list[str]:
    """Decode Git ``-z`` path output without quoting or whitespace loss."""
    return [os.fsdecode(item) for item in output.split(b"\0") if item]


def run_git_paths(args: list[str]) -> tuple[list[str], str | None]:
    proc = subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        raw_detail = proc.stderr.strip() or proc.stdout.strip()
        detail = os.fsdecode(raw_detail) if raw_detail else f"exit {proc.returncode}"
        return [], f"git {' '.join(args)} failed: {detail}"
    return decode_nul_paths(proc.stdout), None


def changed_paths(base: str) -> tuple[set[str], str | None]:
    tracked, error = run_git_paths(
        [
            "diff",
            "--name-only",
            "--no-renames",
            "-z",
            "--diff-filter=ACDMRTUXB",
            base,
            "--",
        ]
    )
    if error is not None:
        return set(), error
    untracked, error = run_git_paths(
        ["ls-files", "--others", "--exclude-standard", "-z"]
    )
    if error is not None:
        return set(), error
    return set(tracked) | set(untracked), None


def reverse_consumers(
    graph: dict[str, set[str]],
    ignored_importers: frozenset[str] = IGNORED_REVERSE_IMPORTERS,
) -> dict[str, set[str]]:
    """Invert imports, omitting edges introduced by flat aggregator modules."""
    reverse: dict[str, set[str]] = defaultdict(set)
    for importer, imports in graph.items():
        if importer in ignored_importers:
            continue
        for imported in imports:
            reverse[imported].add(importer)
    return dict(reverse)


def transitive_reverse_dependents(
    changed_modules: set[str], reverse: dict[str, set[str]]
) -> set[str]:
    affected: set[str] = set()
    work = list(changed_modules)
    while work:
        module = work.pop()
        if module in affected:
            continue
        affected.add(module)
        work.extend(reverse.get(module, set()) - affected)
    return affected


def maximal_affected_targets(
    affected: set[str], reverse: dict[str, set[str]], buildable: set[str]
) -> set[str]:
    """Select affected consumers that have no further affected consumer."""
    maximal = {
        module
        for module in affected
        if not (reverse.get(module, set()) & affected)
    }
    return maximal & buildable


def print_affected_plan(analysis: Analysis, base: str) -> int:
    paths, error = changed_paths(base)
    if error is not None:
        print(f"lean-import-guard --affected: {error}", file=sys.stderr)
        return 3

    config_changes = sorted(path for path in paths if path in FULL_BUILD_PATHS)
    lean_paths = sorted(path for path in paths if path.endswith(".lean"))
    changed_modules = {
        module for path in lean_paths if (module := repo_path_to_module(path)) is not None
    }

    reverse = reverse_consumers(analysis.graph)
    affected = transitive_reverse_dependents(changed_modules, reverse)

    buildable = set(analysis.graph_sources)
    targets = maximal_affected_targets(affected, reverse, buildable)
    outside_verified_libraries = tuple(
        path
        for path in lean_paths
        if path not in FULL_BUILD_PATHS
        and (REPO_ROOT / path).exists()
        and (module := repo_path_to_module(path)) is not None
        and module not in buildable
    )

    print()
    print(f"affected Lean plan (base: {base})")
    print(f"  changed repository paths: {len(paths)}")
    print(f"  changed Lean paths:       {len(lean_paths)}")
    print(f"  changed Lean modules:     {len(changed_modules)}")
    print(f"  reverse-affected modules: {len(affected)}")

    if lean_paths:
        print("changed Lean paths:")
        for path in lean_paths:
            suffix = " (deleted)" if not (REPO_ROOT / path).exists() else ""
            print(f"  - {path}{suffix}")

    if targets:
        print("maximal transitive reverse-dependent targets:")
        for module in sorted(targets):
            print(f"  +{module}")
    else:
        print("maximal transitive reverse-dependent targets: (none)")

    if outside_verified_libraries:
        print("changed Lean sources outside the verified Lake libraries:")
        for path in outside_verified_libraries:
            print(f"  - {path} (requires a separate direct-source check)")

    if config_changes:
        print("FULL BUILD REQUIRED: Lean configuration/toolchain changed:", file=sys.stderr)
        for path in config_changes:
            print(f"  - {path}", file=sys.stderr)
        return 2
    return 0


def self_test() -> int:
    failures: list[str] = []

    def check(label: str, condition: bool) -> None:
        if condition:
            print(f"PASS: {label}")
        else:
            print(f"FAIL: {label}")
            failures.append(label)

    check("YMGap.* matches root", glob_matches("YMGap.*", "YMGap"))
    check("YMGap.* matches submodule", glob_matches("YMGap.*", "YMGap.A.B"))
    check("YMGap.* rejects another root", not glob_matches("YMGap.*", "Other.A"))
    check("YMGap.+ excludes root", not glob_matches("YMGap.+", "YMGap"))
    check("YMGap.+ includes submodule", glob_matches("YMGap.+", "YMGap.A"))

    import_sample = """
/- import YMGap.Commented
   /- import YMGap.Nested -/
-/
import YMGap.Real.One
-- import YMGap.LineComment
import Lean.Elab.Tactic.Omega
public import YMGap.Real.Two
meta import YMGap.Real.Meta
import all
  YMGap.Real.All
import YMGapGuard
def message := "import YMGap.InString"
"""
    check(
        "import parser handles modifiers while ignoring comments, strings, and externals",
        parse_local_imports(import_sample)
        == {
            "YMGap.Real.One",
            "YMGap.Real.Two",
            "YMGap.Real.Meta",
            "YMGap.Real.All",
            "YMGapGuard",
        },
    )

    lake_data: dict[str, object] = {
        "defaultTargets": list(REQUIRED_DEFAULT_TARGETS),
        "lean_lib": [
            {"name": "YMGap", "globs": ["YMGap.*"]},
            {"name": "YMGapGuard"},
            {"name": "YMGapStatementGuard"},
        ],
    }
    lake_coverage, lake_issues = lake_coverage_from_data(lake_data)
    check(
        "Lake coverage accepts the repository build contract",
        lake_coverage.globs == ("YMGap.*",)
        and lake_coverage.default_targets == REQUIRED_DEFAULT_TARGETS
        and not lake_issues,
    )
    _, broken_lake_issues = lake_coverage_from_data(
        {
            "defaultTargets": ["YMGap"],
            "srcDir": "src",
            "lean_lib": [
                {
                    "name": "YMGap",
                    "globs": ["YMGap"],
                    "defaultFacets": [],
                },
                {"name": "YMGapGuard", "roots": ["Other"]},
                {"name": "YMGapStatementGuard", "srcDir": "audit"},
            ],
        }
    )
    check(
        "Lake coverage rejects omitted targets, shifted roots, and inert facets",
        len(broken_lake_issues) == 6,
    )

    encoded_paths = " lean/Leading.lean\0lean/Unicode-λ.lean\0".encode()
    check(
        "NUL Git path decoding preserves whitespace and Unicode",
        decode_nul_paths(encoded_paths)
        == [" lean/Leading.lean", "lean/Unicode-λ.lean"],
    )

    graph = {
        "YMGap": {"YMGap.A", "YMGap.B"},
        "YMGap.A": {"YMGap.Core"},
        "YMGap.B": set(),
        "YMGap.Core": set(),
        "YMGap.Alt": {"YMGap.Alt.Dep"},
        "YMGap.Alt.Dep": set(),
        "YMGap.Loose": set(),
    }
    closure = dependency_closure(graph, {"YMGap"})
    check(
        "dependency closure follows transitive imports",
        closure == {"YMGap", "YMGap.A", "YMGap.B", "YMGap.Core"},
    )
    check(
        "cycle detector finds a canonical witness",
        find_import_cycles({"B": {"C"}, "C": {"A"}, "A": {"B"}, "D": set()})
        == (("A", "B", "C"),),
    )

    manifest, manifest_issues = parse_exclusion_manifest(
        "# reviewed roots\nYMGap.Alt # alternative certificate route\n"
    )
    check(
        "manifest parser accepts documented roots",
        manifest == {"YMGap.Alt": "alternative certificate route"}
        and not manifest_issues,
    )
    _, bad_manifest_issues = parse_exclusion_manifest("YMGap.Bad #\nYMGap.NoReason\n")
    check("manifest parser rejects empty/missing reasons", len(bad_manifest_issues) == 2)

    report = classify_exclusions(set(graph), graph, closure, manifest)
    check(
        "exclusion root classifies its local dependency closure",
        report.classified == {"YMGap.Alt", "YMGap.Alt.Dep"},
    )
    stale_report = classify_exclusions(
        set(graph),
        graph,
        closure,
        {
            "YMGap.Alt": "alternative route",
            "YMGap.Alt.Dep": "redundant nested route",
            "YMGap.A": "already in main root",
            "YMGap.Missing": "not present",
        },
    )
    check("classification detects missing roots", stale_report.missing_roots == ("YMGap.Missing",))
    check("classification detects non-orphan roots", stale_report.non_orphan_roots == ("YMGap.A",))
    check(
        "classification detects stale nested roots",
        stale_report.stale_roots == ("YMGap.Alt.Dep",),
    )

    reverse = reverse_consumers(graph)
    affected = transitive_reverse_dependents({"YMGap.Core"}, reverse)
    targets = maximal_affected_targets(affected, reverse, set(graph))
    check(
        "reverse planner ignores the flat YMGap aggregator edges",
        affected == {"YMGap.Core", "YMGap.A"} and targets == {"YMGap.A"},
    )
    deleted_reverse = reverse_consumers(
        {"YMGap.Consumer": {"YMGap.Deleted"}, "YMGap.Deleted": set()},
        ignored_importers=frozenset(),
    )
    deleted_affected = transitive_reverse_dependents(
        {"YMGap.Deleted"}, deleted_reverse
    )
    check(
        "deleted modules plan their surviving maximal consumers",
        maximal_affected_targets(
            deleted_affected, deleted_reverse, {"YMGap.Consumer"}
        )
        == {"YMGap.Consumer"},
    )
    check(
        "new untracked modules remain directly buildable targets",
        maximal_affected_targets(
            {"YMGap.New"}, {}, {"YMGap.New"}
        )
        == {"YMGap.New"},
    )

    if failures:
        print(f"\nself-test: FAIL ({len(failures)} failure(s))")
        return 1
    print("\nself-test: PASS")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Static Lean import/coverage guard and affected-target planner."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--affected",
        nargs="?",
        const="HEAD",
        metavar="BASE",
        help="also plan maximal reverse-dependent targets (default BASE: HEAD)",
    )
    mode.add_argument(
        "--self-test",
        action="store_true",
        help="run synthetic parser/graph tests without inspecting the repository",
    )
    args = parser.parse_args()

    if args.self_test:
        return self_test()

    analysis = analyze_repository()
    print_analysis(analysis)
    guard_status = 1 if analysis.issues else 0
    if args.affected is not None:
        affected_status = print_affected_plan(analysis, args.affected)
        if affected_status in {2, 3}:
            return affected_status
    return guard_status


if __name__ == "__main__":
    raise SystemExit(main())
