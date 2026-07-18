#!/usr/bin/env python3
"""Reject repository entry points that can start unsafe host workloads.

This is a bounded static check: it never starts Lean, Lake, or pytest.  It
scans Git's tracked files plus untracked/non-ignored files and requires every
repository-provided Lean/Lake/pytest route to use the serialized host wrapper
and one-thread caps.  The few accepted shapes are intentionally visible in the
constants below rather than hidden behind shell evaluation.
"""

from __future__ import annotations

import argparse
import ast
import os
import re
import shlex
import stat
import subprocess
import sys
import warnings
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Iterable, Sequence


ROOT = Path(__file__).resolve().parent.parent
WRAPPER = "with_lean_session_lock.sh"
SHARED_PATTERNS = "scripts/host_load_patterns.sh"
HOST_SCRIPTS = (
    "scripts/with_lean_session_lock.sh",
    "scripts/run_macos_ci_runner.sh",
)
WORKFLOW = ".github/workflows/lean-audit.yml"

MAX_GIT_BYTES = 8 * 1024 * 1024
MAX_FILES = 20_000
MAX_ENTRY_FILES = 2_000
MAX_ENTRY_BYTES = 2 * 1024 * 1024

PY_CAPS = (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "NUMEXPR_NUM_THREADS",
)
SHELL_SUFFIXES = {".sh", ".bash", ".zsh"}
MAKE_NAMES = {"Makefile", "GNUmakefile"}

# Exact non-build exceptions.  The workflow has already verified the pinned
# foreground JIT session lock before these version probes execute.
SHELL_ALLOWLIST = {
    (WORKFLOW, "lean --version"),
    (WORKFLOW, "lake --version"),
}

TOOL = r"(?:[^\s;&|()`]+/)?(?P<tool>lean|lake|pytest|py[.]test)"
PYTEST_MODULE = (
    r"(?:[^\s;&|()`]+/)?python[0-9.]*"
    r"(?:\s+-[^\s;&|()`]+)*\s+-m\s+(?P<module>pytest|py[.]test)"
)
# Only command positions are considered: line/control-substitution starts,
# optional shell keywords/negation, assignments, and ordinary launch prefixes.
DIRECT_SHELL_RE = re.compile(
    rf"(?:^|[;&|(`{{)])\s*[@+-]?\s*"
    rf"(?:(?:if|then|elif|while|until|do|time|command|exec|nohup|!)\s+)*"
    rf"(?:[A-Za-z_][A-Za-z0-9_]*=[^\s;&|()`]+\s+)*"
    rf"(?:(?:(?:[^\s;&|()`]+/)?(?:env|nice|caffeinate))\s+"
    rf"(?:-[^\s;&|()`]+\s+|"
    rf"[A-Za-z_][A-Za-z0-9_]*=[^\s;&|()`]+\s+)*)?"
    rf"(?P<command>{TOOL}|{PYTEST_MODULE})(?=\s|$|[;&|)])"
)
ANY_TOOL_RE = re.compile(
    rf"(?<![A-Za-z0-9_.-])(?:{TOOL}|{PYTEST_MODULE})(?=\s|$|[;&|)])"
)
WRAPPER_RE = re.compile(
    rf"(?:[^\s;&|()`]*{re.escape(WRAPPER)}|\$\(SESSION_LOCK_RUN\))"
)

SHARED_LITERAL_RE = re.compile(
    r"^readonly (?P<name>YMGAP_(?:HIGH_LOAD|RUNNER)_PROCESS_PATTERN)="
    r"(?P<q>['\"])(?P<value>.*)(?P=q)$",
    re.MULTILINE,
)
PGREP_RE = re.compile(r"\bpgrep\s+-if\s+(?P<arg>[^\s\\]+)")

SHARED_COMPOSITION = (
    'readonly YMGAP_CONFLICT_PROCESS_PATTERN="${YMGAP_HIGH_LOAD_PROCESS_PATTERN}'
    '|${YMGAP_RUNNER_PROCESS_PATTERN}"'
)

# These are the only dynamic Python argv shapes accepted by the static gate.
# The path, scope, API, and complete argv shape make each exception narrow and
# review-visible: neither helper can change the named executable before its
# reviewed dynamic tail.
PYTHON_DYNAMIC_PROCESS_ALLOWLIST: dict[tuple[str, str, str], tuple[str, ...]] = {
    (
        "scripts/frontier_burndown.py",
        "read_git_log",
        "subprocess.run",
    ): ("git", "log", "--no-merges", "--name-status", "$<f-string>"),
    (
        "scripts/lean_import_guard.py",
        "run_git_paths",
        "subprocess.run",
    ): ("git", "*$args"),
}

HIGH_LOAD_POSITIVE_PROBES = (
    "lean Example.lean",
    "/Users/me/.elan/bin/lean --version",
    "lake build",
    "/Users/me/.elan/bin/lake build YMGap",
    "pytest -q",
    "/opt/homebrew/bin/pytest tests",
    "py.test -q",
    "/opt/homebrew/bin/py.test tests",
    "python -m pytest",
    "python3 -m pytest -q",
    "/usr/bin/python3.12 -I -m pytest tests",
)
HIGH_LOAD_NEGATIVE_PROBES = (
    "fakelake build",
    "leaning Example.lean",
    "pytester -q",
    "python -m unittest",
    "echo pytest",
)
RUNNER_POSITIVE_PROBES = (
    "/Users/me/actions-runner/bin/Runner.Listener run",
    "/Users/me/actions-runner/bin/Runner.Worker spawnclient 42",
    "/Users/me/actions-runner/bin/Runner.PluginHost action",
    "/bin/bash /Users/me/actions-runner/run.sh",
    "/bin/sh -e /Users/me/actions-runner/run-helper.sh",
    "/bin/bash /Users/me/actions-runner/safe_sleep.sh 1",
    "/bin/bash /Users/me/actions-runner/runsvc.sh",
    "/bin/sh /Users/me/actions-runner/svc.sh start",
    "/bin/bash /Users/me/actions-runner/_work/_update.sh",
    "/bin/bash /Users/me/actions-runner/bin/update.sh",
    "/opt/homebrew/bin/node /Users/me/actions-runner/bin/RunnerService.js",
)
PLUGIN_HOST_PROBE = RUNNER_POSITIVE_PROBES[2]
# These are representative argv strings for the guard itself.  Start anchoring
# must prevent a wrapper's later `lake build` argument—or pgrep's regex
# argument—from making the supervising process conflict with itself.
PROCESS_SELF_NEGATIVE_PROBES = (
    "/bin/bash /repo/scripts/with_lean_session_lock.sh lean env LEAN_NUM_THREADS=1 lake build",
    "/bin/bash -e /repo/scripts/run_macos_ci_runner.sh --check",
    "./scripts/with_lean_session_lock.sh . env OMP_NUM_THREADS=1 pytest",
    "/usr/bin/pgrep -if ^([^[:space:]]*/)?(lean|lake|pytest|py[.]test)",
)
SERVICE_UPDATE_PROBES = RUNNER_POSITIVE_PROBES[6:]


class GuardError(RuntimeError):
    pass


@dataclass(frozen=True, order=True)
class Issue:
    path: str
    line: int
    detail: str

    def render(self) -> str:
        where = self.path if self.line <= 0 else f"{self.path}:{self.line}"
        return f"{where}: {self.detail}"


def is_workflow(relative: str) -> bool:
    path = PurePosixPath(relative)
    return path.parts[:2] == (".github", "workflows") and path.suffix in {".yml", ".yaml"}


def relevant(path: Path, relative: str) -> bool:
    pure = PurePosixPath(relative)
    if pure.name in MAKE_NAMES or pure.suffix in SHELL_SUFFIXES | {".py", ".mk"}:
        return True
    if is_workflow(relative):
        return True
    try:
        mode = path.lstat().st_mode
    except OSError:
        return True  # reader reports a tracked-but-missing file fail-closed
    if stat.S_ISLNK(mode):
        return True  # read_entry rejects executable-route indirection fail-closed
    return stat.S_ISREG(mode) and bool(mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH))


def discover(root: Path) -> list[tuple[str, Path]]:
    proc = subprocess.run(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=root,
        capture_output=True,
        check=False,
    )
    if proc.returncode:
        detail = os.fsdecode(proc.stderr.strip() or proc.stdout.strip())
        raise GuardError(f"git file discovery failed: {detail or proc.returncode}")
    if len(proc.stdout) > MAX_GIT_BYTES:
        raise GuardError("Git file list exceeds the static-scan byte bound")
    raw = [item for item in proc.stdout.split(b"\0") if item]
    if len(raw) > MAX_FILES:
        raise GuardError(f"Git reported {len(raw)} files (limit {MAX_FILES})")

    found: list[tuple[str, Path]] = []
    for item in raw:
        relative = os.fsdecode(item)
        pure = PurePosixPath(relative)
        if pure.is_absolute() or ".." in pure.parts:
            raise GuardError(f"unsafe Git path: {relative!r}")
        path = root.joinpath(*pure.parts)
        if relevant(path, relative):
            found.append((relative, path))
    found = sorted(set(found))
    if len(found) > MAX_ENTRY_FILES:
        raise GuardError(f"found {len(found)} entry files (limit {MAX_ENTRY_FILES})")
    return found


def read_entry(relative: str, path: Path) -> str:
    try:
        info = path.lstat()
    except OSError as exc:
        raise GuardError(f"cannot inspect {relative}: {exc}") from exc
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        raise GuardError(f"entry point must be a regular non-symlink: {relative}")
    if info.st_size > MAX_ENTRY_BYTES:
        raise GuardError(f"entry point exceeds {MAX_ENTRY_BYTES} bytes: {relative}")
    try:
        return path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise GuardError(f"cannot read UTF-8 entry point {relative}: {exc}") from exc


def logical_lines(text: str) -> Iterable[tuple[int, str]]:
    start = 1
    pieces: list[str] = []
    for number, line in enumerate(text.splitlines(), 1):
        if not pieces:
            start = number
        stripped = line.rstrip()
        if stripped.endswith("\\"):
            pieces.append(stripped[:-1])
        else:
            pieces.append(line)
            yield start, " ".join(pieces)
            pieces = []
    if pieces:
        yield start, " ".join(pieces)


def workflow_runs(text: str) -> str:
    """Keep YAML run blocks at their original line numbers; blank metadata."""
    source = text.splitlines()
    result = [""] * len(source)
    index = 0
    run_re = re.compile(r"^(?P<indent>\s*)run:\s*(?P<body>.*)$")
    while index < len(source):
        match = run_re.match(source[index])
        if match is None:
            index += 1
            continue
        indent = len(match.group("indent"))
        body = match.group("body").strip()
        if body not in {"|", "|-", "|+", ">", ">-", ">+"}:
            result[index] = match.group("body")
            index += 1
            continue
        cursor = index + 1
        while cursor < len(source):
            line = source[cursor]
            if line.strip() and len(line) - len(line.lstrip()) <= indent:
                break
            result[cursor] = line
            cursor += 1
        index = cursor
    return "\n".join(result)


def cap_names(line: str) -> set[str]:
    return set(re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*)=1(?:\s|$)", line))


def wrapper_cap_issues(relative: str, number: int, line: str) -> list[Issue]:
    wrapper = WRAPPER_RE.search(line)
    if wrapper is None:
        return []
    tail = line[wrapper.end() :]
    tools = list(ANY_TOOL_RE.finditer(tail))
    if not tools:
        return []
    tool_names = {(match.group("tool") or match.group("module")) for match in tools}
    caps = cap_names(tail)
    issues: list[Issue] = []
    if tool_names & {"lean", "lake"} and "LEAN_NUM_THREADS" not in caps:
        make_macro = relative in MAKE_NAMES and "LEAN_NUM_THREADS=$(LEAN_JOBS)" in tail
        if not make_macro:
            issues.append(
                Issue(
                    relative,
                    number,
                    "serialized Lean/Lake route lacks LEAN_NUM_THREADS=1",
                )
            )
    if tool_names & {"pytest", "py.test"}:
        missing = [name for name in PY_CAPS if name not in caps]
        make_macro = relative in MAKE_NAMES and "$(PYTHON_THREAD_CAPS)" in tail
        if missing and not make_macro:
            issues.append(
                Issue(
                    relative,
                    number,
                    "serialized pytest route lacks cap(s): " + ", ".join(missing),
                )
            )
    return issues


def scan_shell(relative: str, text: str) -> list[Issue]:
    issues: list[Issue] = []
    for number, line in logical_lines(text):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        # The two literal regex declarations and their exact composition are
        # data, not commands.  Mask only those complete declaration lines;
        # everything else in the sourced file is executable shell and must be
        # audited normally (including a command appended after a declaration).
        if relative == SHARED_PATTERNS and (
            SHARED_LITERAL_RE.fullmatch(stripped) is not None
            or stripped == SHARED_COMPOSITION
        ):
            continue
        issues.extend(wrapper_cap_issues(relative, number, line))
        wrapper_spans = [match.span() for match in WRAPPER_RE.finditer(line)]
        for match in DIRECT_SHELL_RE.finditer(line):
            # A Make `$(SESSION_LOCK_RUN)` ends with `)`, itself a valid shell
            # case-command boundary.  Do not reinterpret that character while
            # it is still inside the recognized wrapper token; a later `; lake`
            # remains outside the span and is still rejected.
            if any(start <= match.start() < end for start, end in wrapper_spans):
                continue
            if line[match.start() : match.start() + 1] == ")" and line.rfind(
                "$(", 0, match.start()
            ) > line.rfind(")", 0, match.start()):
                continue
            if (relative, stripped) in SHELL_ALLOWLIST:
                continue
            tool = match.group("tool") or match.group("module")
            issues.append(
                Issue(
                    relative,
                    number,
                    f"direct {tool} route bypasses scripts/{WRAPPER}",
                )
            )
    return issues


def call_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = call_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""


@dataclass(frozen=True)
class ArgToken:
    text: str | None
    literal: bool


def token(node: ast.AST) -> ArgToken:
    """Return a display token while retaining whether its value is literal."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return ArgToken(node.value, True)
    if isinstance(node, ast.Name):
        return ArgToken(f"${node.id}", False)
    if (
        isinstance(node, ast.Call)
        and call_name(node.func) == "str"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    ):
        return ArgToken(f"${node.args[0].id}", False)
    if isinstance(node, ast.Starred) and isinstance(node.value, ast.Name):
        return ArgToken(f"*${node.value.id}", False)
    if isinstance(node, ast.JoinedStr):
        return ArgToken("$<f-string>", False)
    return ArgToken(None, False)


def env_caps(tree: ast.AST) -> dict[str, set[str]]:
    result: dict[str, set[str]] = {}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Assign):
            continue
        if not isinstance(node.value, ast.Constant) or str(node.value.value) != "1":
            continue
        for target in node.targets:
            if not isinstance(target, ast.Subscript) or not isinstance(target.value, ast.Name):
                continue
            if isinstance(target.slice, ast.Constant) and isinstance(target.slice.value, str):
                result.setdefault(target.value.id, set()).add(target.slice.value)
    return result


PROCESS_CALLS = {
    "subprocess.run",
    "subprocess.Popen",
    "subprocess.call",
    "subprocess.check_call",
    "subprocess.check_output",
    "subprocess.getoutput",
    "subprocess.getstatusoutput",
    "asyncio.create_subprocess_exec",
    "asyncio.create_subprocess_shell",
    "os.system",
    "os.popen",
    "os.posix_spawn",
    "os.posix_spawnp",
}

PROCESS_MODULES = {"asyncio", "os", "subprocess"}
SHELL_PROCESS_CALLS = {
    "asyncio.create_subprocess_shell",
    "os.system",
    "os.popen",
    "subprocess.getoutput",
    "subprocess.getstatusoutput",
}
SHELL_EXECUTABLES = {"ash", "bash", "dash", "ksh", "sh", "zsh"}


def import_aliases(tree: ast.AST) -> dict[str, str]:
    """Resolve ordinary import aliases for the process APIs we audit."""
    aliases = {name: name for name in PROCESS_MODULES | {"pytest"}}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for item in node.names:
                if item.name in PROCESS_MODULES | {"pytest"}:
                    aliases[item.asname or item.name] = item.name
        elif isinstance(node, ast.ImportFrom) and node.module in PROCESS_MODULES | {
            "pytest"
        }:
            for item in node.names:
                if item.name != "*":
                    aliases[item.asname or item.name] = f"{node.module}.{item.name}"
    # Also resolve direct, reviewable aliases such as `execute = subprocess.run`.
    # Iterate because a module may itself have first been imported under an alias.
    changed = True
    while changed:
        changed = False
        for node in ast.walk(tree):
            target: ast.AST | None = None
            value: ast.AST | None = None
            if isinstance(node, ast.Assign) and len(node.targets) == 1:
                target, value = node.targets[0], node.value
            elif isinstance(node, ast.AnnAssign):
                target, value = node.target, node.value
            if not isinstance(target, ast.Name) or value is None:
                continue
            resolved = normalized_call_name(value, aliases)
            if not (
                resolved in PROCESS_MODULES
                or is_process_call(resolved)
                or resolved == "pytest.main"
            ):
                continue
            if aliases.get(target.id) != resolved:
                aliases[target.id] = resolved
                changed = True
    return aliases


def normalized_call_name(func: ast.AST, aliases: dict[str, str]) -> str:
    raw = call_name(func)
    head, separator, tail = raw.partition(".")
    replacement = aliases.get(head)
    if replacement is None:
        return raw
    return replacement + (separator + tail if separator else "")


def is_process_call(name: str) -> bool:
    return name in PROCESS_CALLS or re.fullmatch(
        r"os[.](?:exec|spawn)[A-Za-z0-9_]*", name
    ) is not None


def process_command(call: ast.Call, name: str) -> ast.AST | None:
    # os.spawn* has a leading mode argument; every other accepted API names
    # its executable/command first.  The executable path itself is decisive
    # for os.exec*/posix_spawn*, so their separate argv need not be guessed.
    index = 1 if re.fullmatch(r"os[.]spawn[A-Za-z0-9_]*", name) else 0
    return call.args[index] if len(call.args) > index else None


def shell_keyword(call: ast.Call) -> bool | None:
    for keyword in call.keywords:
        if keyword.arg != "shell":
            continue
        if isinstance(keyword.value, ast.Constant) and isinstance(
            keyword.value.value, bool
        ):
            return keyword.value.value
        return None
    return False


def argv_basename(item: ArgToken) -> str | None:
    return item.text.rsplit("/", 1)[-1] if item.text is not None else None


def resolve_launch_executable(argv: Sequence[ArgToken]) -> tuple[int | None, str | None]:
    """Resolve only transparent, literal launch prefixes; fail closed otherwise."""
    index = 0
    while index < len(argv):
        current = argv[index]
        if not current.literal or current.text is None:
            return None, "dynamic executable or launch prefix"
        executable = argv_basename(current)
        if executable == "env":
            index += 1
            while index < len(argv):
                item = argv[index]
                if not item.literal or item.text is None:
                    return None, "dynamic env launch prefix"
                value = item.text
                if "=" in value and not value.startswith("="):
                    index += 1
                    continue
                if value in {"-i", "--ignore-environment"} or value.startswith(
                    ("--unset=", "--chdir=")
                ):
                    index += 1
                    continue
                if value in {"-u", "--unset", "-C", "--chdir"}:
                    if index + 1 >= len(argv) or not argv[index + 1].literal:
                        return None, "dynamic or incomplete env option"
                    index += 2
                    continue
                if value.startswith("-"):
                    return None, f"unsupported env dispatcher option {value!r}"
                break
            continue
        if executable == "nice":
            index += 1
            while index < len(argv):
                item = argv[index]
                if not item.literal or item.text is None:
                    return None, "dynamic nice launch prefix"
                value = item.text
                if value in {"-n", "--adjustment"}:
                    if index + 1 >= len(argv) or not argv[index + 1].literal:
                        return None, "dynamic or incomplete nice adjustment"
                    index += 2
                    continue
                if value.startswith("-"):
                    index += 1
                    continue
                break
            continue
        if executable == "caffeinate":
            index += 1
            while index < len(argv):
                item = argv[index]
                if not item.literal or item.text is None:
                    return None, "dynamic caffeinate launch prefix"
                value = item.text
                if value in {"-t", "-w"}:
                    if index + 1 >= len(argv) or not argv[index + 1].literal:
                        return None, "dynamic or incomplete caffeinate option"
                    index += 2
                    continue
                if value.startswith("-"):
                    index += 1
                    continue
                break
            continue
        if executable in {"nohup", "time"}:
            index += 1
            while index < len(argv):
                item = argv[index]
                if not item.literal or item.text is None:
                    return None, f"dynamic {executable} launch prefix"
                if item.text.startswith("-"):
                    index += 1
                    continue
                break
            continue
        return index, None
    return None, "launch prefix has no executable"


def dynamic_process_allowlisted(
    relative: str,
    scope: str,
    name: str,
    argv: Sequence[ArgToken],
) -> bool:
    prefix = PYTHON_DYNAMIC_PROCESS_ALLOWLIST.get((relative, scope, name))
    if prefix is None or len(argv) != len(prefix):
        return False
    return tuple(item.text for item in argv) == prefix


def python_process_issue(
    relative: str,
    scope: str,
    name: str,
    call: ast.Call,
    known_caps: dict[str, set[str]],
) -> Issue | None:
    if not is_process_call(name):
        return None
    for keyword in call.keywords:
        if keyword.arg != "executable":
            continue
        if isinstance(keyword.value, ast.Constant) and keyword.value.value is None:
            continue
        if not (
            isinstance(keyword.value, ast.Constant)
            and isinstance(keyword.value.value, str)
        ):
            return Issue(
                relative,
                call.lineno,
                f"{name} has a dynamic executable= override",
            )
        nested = scan_shell(relative, keyword.value.value)
        if nested:
            return Issue(relative, call.lineno, nested[0].detail)
    command = process_command(call, name)
    if command is None:
        return Issue(relative, call.lineno, f"{name} has no statically inspectable command")
    uses_shell = name in SHELL_PROCESS_CALLS
    explicit_shell = shell_keyword(call)
    if explicit_shell is None:
        return Issue(relative, call.lineno, f"{name} has a dynamic shell= setting")
    uses_shell = uses_shell or explicit_shell
    if isinstance(command, ast.Constant) and isinstance(command.value, str):
        # A literal shell string can be audited directly.  Conservatively scan
        # literal executable strings too: rejecting `"lake build"` when
        # shell=False is harmless and prevents a future shell=True edit from
        # opening a gap.
        nested = scan_shell(relative, command.value)
        return Issue(relative, call.lineno, nested[0].detail) if nested else None
    if not isinstance(command, (ast.List, ast.Tuple)):
        return Issue(
            relative,
            call.lineno,
            f"dynamic {name} command is not statically proven host-safe",
        )
    argv = [token(item) for item in command.elts]
    if not argv:
        return Issue(relative, call.lineno, f"{name} has an empty argv")
    first = argv_basename(argv[0])
    is_wrapper = first is not None and (
        WRAPPER in first or first == "$SESSION_LOCK_RUN"
    )
    if is_wrapper:
        if uses_shell:
            return Issue(relative, call.lineno, "serialized Python route may not use shell=True")
        if len(argv) < 3:
            return Issue(relative, call.lineno, "serialized Python route lacks workdir/command")
        command_index, error = resolve_launch_executable(argv[2:])
        if command_index is None:
            return Issue(
                relative,
                call.lineno,
                f"serialized Python route has {error or 'an unresolved command'}",
            )
        command_index += 2
        executable = argv_basename(argv[command_index])
        if executable in SHELL_EXECUTABLES:
            return Issue(
                relative,
                call.lineno,
                "serialized Python route hides its command behind a shell",
            )
        if executable not in {"lean", "lake", "pytest", "py.test"}:
            is_python = executable is not None and re.fullmatch(
                r"python[0-9.]*", executable
            )
            literal_tail = [item.text for item in argv[command_index:] if item.literal]
            if not (
                is_python
                and any(
                    literal_tail[index : index + 2] in (["-m", "pytest"], ["-m", "py.test"])
                    for index in range(max(0, len(literal_tail) - 1))
                )
            ):
                # The executable is statically known not to be a guarded host
                # workload.  Dynamic trailing arguments cannot replace it.
                return None
            executable = "pytest"
        tool = executable
        if tool is None:
            return None
        inherited: set[str] = set()
        for keyword in call.keywords:
            if keyword.arg == "env" and isinstance(keyword.value, ast.Name):
                inherited = known_caps.get(keyword.value.id, set())
        required = {"LEAN_NUM_THREADS"} if tool in {"lean", "lake"} else set(PY_CAPS)
        joined = " ".join(item.text for item in argv if item.text is not None)
        missing = sorted(required - inherited - cap_names(joined))
        if missing:
            return Issue(
                relative,
                call.lineno,
                f"serialized Python {tool} route lacks cap(s): " + ", ".join(missing),
            )
        return None

    if uses_shell:
        return Issue(
            relative,
            call.lineno,
            f"{name} uses a non-literal shell command",
        )
    if any(not item.literal for item in argv) and not dynamic_process_allowlisted(
        relative, scope, name, argv
    ):
        return Issue(
            relative,
            call.lineno,
            f"dynamic {name} argv is not explicitly host-safe",
        )
    index, error = resolve_launch_executable(argv)
    if index is None:
        return Issue(relative, call.lineno, f"cannot resolve {name} argv: {error}")
    executable = argv_basename(argv[index])
    if executable is None:
        return Issue(relative, call.lineno, f"cannot resolve {name} executable")
    if executable in {"lean", "lake", "pytest", "py.test"}:
        return Issue(
            relative,
            call.lineno,
            f"Python launches {executable} without scripts/{WRAPPER}",
        )
    is_python = re.fullmatch(r"python[0-9.]*", executable)
    tail = [item.text for item in argv[index:] if item.text is not None]
    is_pytest_module = any(
        tail[position : position + 2] in (["-m", "pytest"], ["-m", "py.test"])
        for position in range(max(0, len(tail) - 1))
    )
    if is_python and is_pytest_module:
        return Issue(relative, call.lineno, f"Python launches pytest without scripts/{WRAPPER}")
    if executable in SHELL_EXECUTABLES:
        try:
            command_position = tail.index("-c") + 1
        except ValueError:
            return None  # literal script path/arguments; the entry point is scanned separately
        if command_position >= len(tail):
            return Issue(relative, call.lineno, "shell -c route has no command")
        nested = scan_shell(relative, tail[command_position])
        if nested:
            return Issue(relative, call.lineno, nested[0].detail)
    return None


def scan_python(relative: str, text: str) -> list[Issue]:
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", SyntaxWarning)
            tree = ast.parse(text, filename=relative)
    except SyntaxError as exc:
        return [Issue(relative, exc.lineno or 0, f"cannot parse Python: {exc.msg}")]
    aliases = import_aliases(tree)
    caps = env_caps(tree)
    issues: list[Issue] = []
    for node in ast.walk(tree):
        if (
            isinstance(node, ast.ImportFrom)
            and node.module in PROCESS_MODULES
            and any(item.name == "*" for item in node.names)
        ):
            issues.append(
                Issue(
                    relative,
                    node.lineno,
                    f"wildcard {node.module} import prevents static process-call proof",
                )
            )

    class CallVisitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.scope: list[str] = []

        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            self.scope.append(node.name)
            self.generic_visit(node)
            self.scope.pop()

        def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
            self.scope.append(node.name)
            self.generic_visit(node)
            self.scope.pop()

        def visit_Lambda(self, node: ast.Lambda) -> None:
            self.scope.append("<lambda>")
            self.generic_visit(node)
            self.scope.pop()

        def visit_Call(self, node: ast.Call) -> None:
            name = normalized_call_name(node.func, aliases)
            if name == "__import__" and node.args:
                module = node.args[0]
                if not (
                    isinstance(module, ast.Constant)
                    and isinstance(module.value, str)
                    and module.value not in PROCESS_MODULES
                ):
                    issues.append(
                        Issue(
                            relative,
                            node.lineno,
                            "dynamic import cannot prove process APIs are host-safe",
                        )
                    )
            if name == "getattr" and node.args:
                owner = normalized_call_name(node.args[0], aliases)
                if owner in PROCESS_MODULES:
                    selected = node.args[1] if len(node.args) > 1 else None
                    selected_name = (
                        selected.value
                        if isinstance(selected, ast.Constant)
                        and isinstance(selected.value, str)
                        else None
                    )
                    process_attribute = selected_name is None or (
                        f"{owner}.{selected_name}" in PROCESS_CALLS
                        or (
                            owner == "os"
                            and re.fullmatch(r"(?:exec|spawn)[A-Za-z0-9_]*", selected_name)
                            is not None
                        )
                    )
                    if process_attribute:
                        issues.append(
                            Issue(
                                relative,
                                node.lineno,
                                f"dynamic {owner} process-API lookup is not statically auditable",
                            )
                        )
            if name == "pytest.main":
                issues.append(
                    Issue(relative, node.lineno, f"pytest.main bypasses scripts/{WRAPPER}")
                )
            issue = python_process_issue(
                relative,
                ".".join(self.scope) or "<module>",
                name,
                node,
                caps,
            )
            if issue:
                issues.append(issue)
            self.generic_visit(node)

    CallVisitor().visit(tree)
    return issues


def compile_posix_ere(pattern: str) -> re.Pattern[str]:
    translated = pattern.replace("[^[:space:]]", r"[^\s]").replace("[[:space:]]", r"\s")
    if "[:" in translated:
        raise GuardError(f"unsupported POSIX class in {pattern!r}")
    try:
        return re.compile(translated, re.IGNORECASE)
    except re.error as exc:
        raise GuardError(f"invalid process pattern: {exc}") from exc


def pattern_probe_failures(
    pattern: str,
    positives: Sequence[str],
    negatives: Sequence[str],
) -> tuple[list[str], list[str]]:
    compiled = compile_posix_ere(pattern)
    missed = [probe for probe in positives if not compiled.search(probe)]
    false_hits = [probe for probe in negatives if compiled.search(probe)]
    return missed, false_hits


def shared_pattern_structure_issues(text: str) -> list[Issue]:
    """The sourced data file may contain comments and its three declarations only."""
    issues: list[Issue] = []
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if (
            SHARED_LITERAL_RE.fullmatch(stripped) is not None
            or stripped == SHARED_COMPOSITION
        ):
            continue
        issues.append(
            Issue(
                SHARED_PATTERNS,
                number,
                "shared pattern file may contain only comments and exact pattern declarations",
            )
        )
    return issues


def validate_patterns(texts: dict[str, str]) -> list[Issue]:
    issues: list[Issue] = []
    shared = texts.get(SHARED_PATTERNS, "")
    issues.extend(shared_pattern_structure_issues(shared))
    literals = {
        match.group("name"): match.group("value")
        for match in SHARED_LITERAL_RE.finditer(shared)
    }
    required = {"YMGAP_HIGH_LOAD_PROCESS_PATTERN", "YMGAP_RUNNER_PROCESS_PATTERN"}
    if set(literals) != required:
        issues.append(
            Issue(
                SHARED_PATTERNS,
                0,
                "must define exactly the shared high-load and runner literals",
            )
        )
    high = literals.get("YMGAP_HIGH_LOAD_PROCESS_PATTERN")
    if high:
        try:
            missed, false = pattern_probe_failures(
                high,
                HIGH_LOAD_POSITIVE_PROBES,
                HIGH_LOAD_NEGATIVE_PROBES + RUNNER_POSITIVE_PROBES,
            )
        except GuardError as exc:
            issues.append(Issue(SHARED_PATTERNS, 0, str(exc)))
        else:
            if missed:
                issues.append(
                    Issue(
                        SHARED_PATTERNS,
                        0,
                        "high-load pattern misses: " + ", ".join(map(repr, missed)),
                    )
                )
            if false:
                issues.append(
                    Issue(
                        SHARED_PATTERNS,
                        0,
                        "high-load pattern false-hits: " + ", ".join(map(repr, false)),
                    )
                )
    runner = literals.get("YMGAP_RUNNER_PROCESS_PATTERN")
    if runner:
        try:
            missed, false = pattern_probe_failures(
                runner, RUNNER_POSITIVE_PROBES, PROCESS_SELF_NEGATIVE_PROBES
            )
        except GuardError as exc:
            issues.append(Issue(SHARED_PATTERNS, 0, str(exc)))
        else:
            if missed:
                issues.append(
                    Issue(
                        SHARED_PATTERNS,
                        0,
                        "runner pattern misses: " + ", ".join(map(repr, missed)),
                    )
                )
            if false:
                issues.append(
                    Issue(
                        SHARED_PATTERNS,
                        0,
                        "runner pattern self-matches: " + ", ".join(map(repr, false)),
                    )
                )
    if high and runner:
        try:
            _, false = pattern_probe_failures(
                f"{high}|{runner}", (), PROCESS_SELF_NEGATIVE_PROBES
            )
        except GuardError as exc:
            issues.append(Issue(SHARED_PATTERNS, 0, str(exc)))
        else:
            if false:
                issues.append(
                    Issue(
                        SHARED_PATTERNS,
                        0,
                        "combined pattern self-matches: " + ", ".join(map(repr, false)),
                    )
                )
    if SHARED_COMPOSITION not in shared:
        issues.append(
            Issue(
                SHARED_PATTERNS,
                0,
                "combined process pattern is not the exact shared composition",
            )
        )

    for relative in HOST_SCRIPTS:
        text = texts.get(relative, "")
        if text.count('source "$script_dir/host_load_patterns.sh"') != 1:
            issues.append(Issue(relative, 0, "must source shared process patterns exactly once"))
        if text.count('readonly conflict_pattern="$YMGAP_CONFLICT_PROCESS_PATTERN"') != 1:
            issues.append(
                Issue(
                    relative,
                    0,
                    "must bind the shared combined conflict pattern exactly once",
                )
            )
        if relative == "scripts/with_lean_session_lock.sh":
            # In inherited CI mode the foreground runner is expected, while a
            # pre-existing Lean/Lake/pytest process is not.  Prove this is the
            # sole high-load-only inspection, that its clear branch execs the
            # wrapped command immediately, and that every top-level inspection
            # retains the combined runner + high-load conflict pattern.
            inherited_marker = 'if [[ "${YMGAP_LEAN_SESSION_LOCK_HELD:-}" == "1" ]]; then'
            inherited_start = text.find(inherited_marker)
            inherited_end = text.find("\nfi\n", inherited_start)
            if inherited_start < 0 or inherited_end < 0:
                issues.append(Issue(relative, 0, "cannot locate the inherited-lock branch"))
                inherited_block = ""
                top_level_text = text
            else:
                inherited_end += len("\nfi\n")
                inherited_block = text[inherited_start:inherited_end]
                top_level_text = text[:inherited_start] + text[inherited_end:]
            inherited_args = [
                match.group("arg") for match in PGREP_RE.finditer(inherited_block)
            ]
            top_level_args = [
                match.group("arg") for match in PGREP_RE.finditer(top_level_text)
            ]
            if inherited_args != ['"$YMGAP_HIGH_LOAD_PROCESS_PATTERN"']:
                issues.append(
                    Issue(
                        relative,
                        0,
                        "inherited-lock branch must perform exactly one "
                        "shared high-load-only pgrep check",
                    )
                )
            if inherited_block.count('1) exec "$@" ;;') != 1:
                issues.append(
                    Issue(
                        relative,
                        0,
                        "inherited-lock clear result must immediately exec the wrapped command",
                    )
                )
            if not top_level_args or any(
                arg != '"$conflict_pattern"' for arg in top_level_args
            ):
                issues.append(
                    Issue(
                        relative,
                        0,
                        "every top-level pgrep workload check must use $conflict_pattern",
                    )
                )
        else:
            args = [match.group("arg") for match in PGREP_RE.finditer(text)]
            if not args or any(arg != '"$conflict_pattern"' for arg in args):
                issues.append(
                    Issue(
                        relative,
                        0,
                        "every pgrep workload check must use $conflict_pattern",
                    )
                )

    workflow = texts.get(WORKFLOW, "")
    args = [match.group("arg") for match in PGREP_RE.finditer(workflow)]
    if not args or any(arg != '"$YMGAP_HIGH_LOAD_PROCESS_PATTERN"' for arg in args):
        issues.append(
            Issue(
                WORKFLOW,
                0,
                "every workflow pgrep check must use the shared high-load pattern",
            )
        )
    if workflow.count("source scripts/host_load_patterns.sh") != len(args):
        issues.append(
            Issue(
                WORKFLOW,
                0,
                "each workflow pgrep run block must source shared patterns",
            )
        )
    return issues


def validate_make(text: str) -> list[Issue]:
    issues: list[Issue] = []
    required = (
        "override SESSION_LOCK_RUN := ./scripts/with_lean_session_lock.sh",
        "ifneq ($(strip $(LEAN_JOBS)),1)",
        "override LEAN_JOBS := 1",
    )
    for literal in required:
        if text.count(literal) != 1:
            issues.append(
                Issue(
                    "Makefile",
                    0,
                    f"required host-cap declaration is not unique: {literal}",
                )
            )
    joined = "\n".join(line for _, line in logical_lines(text))
    declaration = next(
        (line for line in joined.splitlines() if "PYTHON_THREAD_CAPS :=" in line),
        "",
    )
    missing = [name for name in PY_CAPS if f"{name}=1" not in declaration]
    if missing:
        issues.append(Issue("Makefile", 0, "PYTHON_THREAD_CAPS misses: " + ", ".join(missing)))
    return issues


def executable_interpreter(text: str) -> tuple[str | None, str | None]:
    """Classify an executable entry point from its shebang, fail-closed."""
    first_line = text.splitlines()[0] if text.splitlines() else ""
    if not first_line.startswith("#!"):
        return None, "executable entry point has no shebang"
    try:
        words = shlex.split(first_line[2:].strip(), posix=True)
    except ValueError as exc:
        return None, f"cannot parse executable shebang: {exc}"
    if not words:
        return None, "executable entry point has an empty shebang"
    interpreter = words[0].rsplit("/", 1)[-1]
    if interpreter == "env":
        index = 1
        while index < len(words):
            value = words[index]
            if value in {"-i", "--ignore-environment", "-S", "--split-string"}:
                index += 1
                continue
            if value.startswith(("--unset=", "--chdir=")) or "=" in value:
                index += 1
                continue
            if value in {"-u", "--unset", "-C", "--chdir"}:
                index += 2
                continue
            if value.startswith("-"):
                return None, f"unsupported executable env shebang option {value!r}"
            break
        if index >= len(words):
            return None, "executable env shebang has no interpreter"
        interpreter = words[index].rsplit("/", 1)[-1]
    if interpreter in SHELL_EXECUTABLES:
        return "shell", None
    if re.fullmatch(r"python[0-9.]*", interpreter):
        return "python", None
    return None, f"unsupported executable interpreter {interpreter!r}"


def scan_entry_text(relative: str, text: str, *, executable: bool) -> list[Issue]:
    """Dispatch every discovered entry point to a real parser/scanner."""
    pure = PurePosixPath(relative)
    if pure.suffix == ".py":
        return scan_python(relative, text)
    if pure.suffix in SHELL_SUFFIXES | {".mk"} or pure.name in MAKE_NAMES:
        return scan_shell(relative, text)
    if is_workflow(relative):
        return scan_shell(relative, workflow_runs(text))
    if not executable:
        # `relevant` admits non-executables only through one of the cases above.
        return [Issue(relative, 0, "entry point has no static scanner")]
    kind, error = executable_interpreter(text)
    if kind == "python":
        return scan_python(relative, text)
    if kind == "shell":
        return scan_shell(relative, text)
    return [Issue(relative, 1, error or "cannot classify executable entry point")]


def scan_repository(root: Path = ROOT) -> tuple[list[Issue], int]:
    entries = discover(root)
    texts: dict[str, str] = {}
    issues: list[Issue] = []
    for relative, path in entries:
        try:
            text = read_entry(relative, path)
        except GuardError as exc:
            issues.append(Issue(relative, 0, str(exc)))
            continue
        texts[relative] = text
        try:
            executable = bool(
                path.lstat().st_mode
                & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
            )
        except OSError as exc:
            issues.append(Issue(relative, 0, f"cannot re-inspect entry point mode: {exc}"))
            continue
        issues.extend(scan_entry_text(relative, text, executable=executable))
    issues.extend(validate_patterns(texts))
    issues.extend(validate_make(texts.get("Makefile", "")))
    return sorted(set(issues)), len(entries)


def self_test() -> None:
    def expect(count: int, issues: Sequence[Issue], label: str) -> None:
        if len(issues) != count:
            rendered = "\n".join(issue.render() for issue in issues)
            raise AssertionError(f"{label}: expected {count}, got {len(issues)}\n{rendered}")

    # These are the two concrete regressions which motivated the static gate.
    expect(
        1,
        scan_shell(
            "computations/progress_metric.sh", "GUARD=$(lake build YMGapGuard)"
        ),
        "bare Lake",
    )
    expect(
        1,
        scan_python(
            "tests/test_wigner_6j.py", "import pytest\npytest.main([__file__])"
        ),
        "pytest.main",
    )
    expect(
        1,
        scan_python(
            "x.py",
            'import subprocess\nsubprocess.run('
            '["env", "LEAN_NUM_THREADS=1", "lake", "build"])',
        ),
        "capped but unlocked Python",
    )
    expect(1, scan_shell("x.sh", "env LEAN_NUM_THREADS=1 lake build"), "capped but unlocked")
    expect(
        1,
        scan_shell("x.sh", "if lake build; then :; fi"),
        "shell if control route",
    )
    expect(
        1,
        scan_shell("x.sh", "if ! lake build; then :; fi"),
        "shell negated if control route",
    )
    expect(1, scan_shell("x.sh", "! lake build"), "shell negated route")
    expect(
        1,
        scan_shell("x.sh", "./scripts/with_lean_session_lock.sh lean lake build"),
        "locked but uncapped",
    )

    safe_shell = (
        "./scripts/with_lean_session_lock.sh lean env LEAN_NUM_THREADS=1 lake build\n"
        "./scripts/with_lean_session_lock.sh . env "
        + " ".join(f"{name}=1" for name in PY_CAPS)
        + " pytest\n"
    )
    expect(0, scan_shell("x.sh", safe_shell), "safe wrappers")

    pattern_data = (
        "readonly YMGAP_HIGH_LOAD_PROCESS_PATTERN='^lake$'\n"
        "readonly YMGAP_RUNNER_PROCESS_PATTERN='^Runner[.]Listener$'\n"
        + SHARED_COMPOSITION
        + "\n"
    )
    expect(
        0,
        scan_shell(SHARED_PATTERNS, pattern_data),
        "shared declarations are data",
    )
    expect(
        0,
        shared_pattern_structure_issues(pattern_data),
        "shared declaration-only structure",
    )
    expect(
        1,
        scan_shell(SHARED_PATTERNS, pattern_data + "if ! lake build; then :; fi\n"),
        "shared pattern file appended command",
    )
    expect(
        1,
        scan_shell(
            SHARED_PATTERNS,
            "readonly YMGAP_HIGH_LOAD_PROCESS_PATTERN='^lake$'; lake build\n",
        ),
        "shared pattern declaration trailing command",
    )
    expect(
        1,
        shared_pattern_structure_issues(pattern_data + "echo safe\n"),
        "shared pattern file rejects non-declaration statements",
    )
    expect(0, scan_shell(WORKFLOW, "lean --version\nlake --version"), "version allowlist")
    expect(2, scan_shell("x.sh", "lean --version\nlake --version"), "narrow version allowlist")

    safe_python = """
import subprocess
SESSION_LOCK_RUN = object()
LEAN_DIR = object()
env = {}
env["LEAN_NUM_THREADS"] = "1"
subprocess.run([str(SESSION_LOCK_RUN), str(LEAN_DIR), "lake", "build"], env=env)
"""
    expect(0, scan_python("x.py", safe_python), "safe Python wrapper")

    dynamic_python_probes = {
        "dynamic subprocess command": """
import subprocess
command = ["lake", "build"]
subprocess.run(command)
""",
        "dynamic subprocess f-string": """
import subprocess
target = "build"
subprocess.run(f"lake {target}", shell=True)
""",
        "aliased subprocess command": """
import subprocess as process
command = ["lake", "build"]
process.run(command)
""",
        "from-import subprocess command": """
from subprocess import run as execute
command = ["lake", "build"]
execute(command)
""",
        "assigned subprocess alias": """
import subprocess
execute = subprocess.run
command = ["lake", "build"]
execute(command)
""",
        "dynamic os.system command": """
import os
command = "lake build"
os.system(command)
""",
        "dynamic shell -c command": """
import subprocess
command = "lake build"
subprocess.run(["bash", "-c", command])
""",
        "dynamic env argv": """
import subprocess
command = ["lake", "build"]
subprocess.run(["env", *command])
""",
        "dynamic shell keyword": """
import subprocess
use_shell = False
subprocess.run(["git", "status"], shell=use_shell)
""",
        "dynamic executable override": """
import subprocess
program = "lake"
subprocess.run(["build"], executable=program)
""",
        "static unsafe executable override": """
import subprocess
subprocess.run(["build"], executable="lake")
""",
        "static nested shell workload": """
import subprocess
subprocess.run(["bash", "-c", "if ! lake build; then exit 1; fi"])
""",
    }
    for label, source in dynamic_python_probes.items():
        expect(1, scan_python("x.py", source), label)

    expect(
        0,
        scan_python(
            "x.py",
            'import subprocess\nsubprocess.run(["git", "status"])\n',
        ),
        "static safe Python argv",
    )
    expect(
        0,
        scan_python(
            "x.py",
            'import subprocess\nsubprocess.run(["echo", "lake"])\n',
        ),
        "tool word is a safe argv argument",
    )
    expect(
        0,
        scan_python("x.py", 'import os\nos.system("echo safe")\n'),
        "static safe shell string",
    )
    expect(
        0,
        scan_python(
            "scripts/lean_import_guard.py",
            """
import subprocess
def run_git_paths(args):
    return subprocess.run(["git", *args])
""",
        ),
        "narrow dynamic Git allowlist",
    )
    expect(
        1,
        scan_python(
            "scripts/lean_import_guard.py",
            """
import subprocess
def different_scope(args):
    return subprocess.run(["git", *args])
""",
        ),
        "dynamic Git wrong-scope rejection",
    )
    expect(
        1,
        scan_python(
            "scripts/lean_import_guard.py",
            """
import subprocess
def run_git_paths(args):
    return subprocess.run(["bash", *args])
""",
        ),
        "dynamic Git allowlist prefix mutation",
    )

    expect(
        1,
        scan_entry_text(
            "tools/build",
            "#!/bin/sh\nif ! lake build; then exit 1; fi\n",
            executable=True,
        ),
        "extensionless executable shell route",
    )
    expect(
        1,
        scan_entry_text(
            "tools/build",
            "#!/usr/bin/env python3\nimport subprocess\nsubprocess.run(command)\n",
            executable=True,
        ),
        "extensionless executable Python route",
    )
    expect(
        1,
        scan_entry_text("tools/build", "lake build\n", executable=True),
        "extensionless executable missing shebang",
    )
    expect(
        0,
        scan_entry_text(
            "tools/build",
            "#!/usr/bin/env bash\n" + safe_shell,
            executable=True,
        ),
        "safe extensionless executable wrapper",
    )

    complete = (
        r"^([^[:space:]]*/)?(lean|lake|pytest|py[.]test)([[:space:]]|$)"
        r"|^([^[:space:]]*/)?python[0-9.]*([[:space:]]+-[^[:space:]]+)*"
        r"[[:space:]]+-m[[:space:]]+pytest([[:space:]]|$)"
    )
    regex = compile_posix_ere(complete)
    if any(not regex.search(probe) for probe in HIGH_LOAD_POSITIVE_PROBES):
        raise AssertionError("complete process pattern missed a positive probe")
    if any(
        regex.search(probe)
        for probe in HIGH_LOAD_NEGATIVE_PROBES + RUNNER_POSITIVE_PROBES
    ):
        raise AssertionError("complete process pattern hit a negative probe")
    incomplete = compile_posix_ere(r"^(lean|lake|pytest)([[:space:]]|$)")
    if all(incomplete.search(probe) for probe in HIGH_LOAD_POSITIVE_PROBES):
        raise AssertionError("incomplete process pattern unexpectedly covered all probes")

    complete_runner = (
        r"^([^[:space:]]*/)?Runner[.](Listener|Worker|PluginHost)([[:space:]]|$)"
        r"|^([^[:space:]]*/)?(bash|sh)([[:space:]]+-[^[:space:]]+)*"
        r"[[:space:]]+([^[:space:]]*/)?"
        r"(run[.]sh|run-helper[.]sh|safe_sleep[.]sh|runsvc[.]sh|svc[.]sh|"
        r"_update[.]sh|update[.]sh)([[:space:]]|$)"
        r"|^([^[:space:]]*/)?node[0-9.]*([[:space:]]+-[^[:space:]]+)*"
        r"[[:space:]]+([^[:space:]]*/)?RunnerService[.]js([[:space:]]|$)"
    )
    missed, false = pattern_probe_failures(
        complete_runner, RUNNER_POSITIVE_PROBES, PROCESS_SELF_NEGATIVE_PROBES
    )
    if missed or false:
        raise AssertionError(
            f"complete runner pattern probe failure: missed={missed!r}, false={false!r}"
        )

    # Deliberately omit PluginHost, service supervisors, and both updater forms.
    # Every corresponding regression probe must be rejected.
    incomplete_runner = (
        r"^([^[:space:]]*/)?Runner[.](Listener|Worker)([[:space:]]|$)"
        r"|^([^[:space:]]*/)?(bash|sh)([[:space:]]+-[^[:space:]]+)*"
        r"[[:space:]]+([^[:space:]]*/)?"
        r"(run[.]sh|run-helper[.]sh|safe_sleep[.]sh)([[:space:]]|$)"
    )
    missed, _ = pattern_probe_failures(
        incomplete_runner, RUNNER_POSITIVE_PROBES, PROCESS_SELF_NEGATIVE_PROBES
    )
    if not set(SERVICE_UPDATE_PROBES + (PLUGIN_HOST_PROBE,)).issubset(missed):
        raise AssertionError(
            "runner pattern missing PluginHost/updater/service forms was not rejected by all probes"
        )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        try:
            self_test()
        except (AssertionError, GuardError) as exc:
            print(f"host-load-guard self-test FAILED: {exc}", file=sys.stderr)
            return 2
        print("host-load-guard self-test: PASS")
        return 0
    try:
        issues, count = scan_repository()
    except GuardError as exc:
        print(f"host-load-guard FAILED: {exc}", file=sys.stderr)
        return 2
    if issues:
        print("host-load-guard FAILED:", file=sys.stderr)
        for issue in issues:
            print(f"  - {issue.render()}", file=sys.stderr)
        print(f"scanned {count} entry files; found {len(issues)} issue(s)", file=sys.stderr)
        return 1
    print(f"host-load-guard: PASS ({count} tracked/untracked non-ignored entry files)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
