#!/usr/bin/env python3
"""Run Lean with crash-resistant concurrency and memory-pressure guards.

The 2026-08-02 incident was a watchdog kernel panic during a three-worker
``lake build`` on a 64 GiB Mac.  Each worker was allowed 32 GiB, so the
aggregate allowance exceeded physical memory and filled the compressor's
segment pool.  This launcher is the single supported entry point for Lean
builds and one-file checks in this repository.

It provides four independent protections:

* two workers on machines with at least 48 GiB (one on smaller machines),
  with unsafe parallelism rejected at preflight;
* a repository lock that prevents competing monitored Lean builds;
* periodic RAM, memory-pressure, swap, and build-tree RSS checks; and
* process-group shutdown before the operating system becomes unresponsive.

Use ``python3 scripts/safe_lean_build.py -- TARGET`` for a Lake target, or
``python3 scripts/safe_lean_build.py --check lean/path/File.lean`` for a
single-file elaboration check.  Do not bypass this launcher with bare
``lake build`` or ``lake env lean`` commands.
"""

from __future__ import annotations

import argparse
import fcntl
import os
import platform
import re
import signal
import subprocess
import sys
import time
from collections.abc import Iterator, Sequence
from contextlib import AbstractContextManager, contextmanager, nullcontext
from dataclasses import dataclass
from pathlib import Path
from typing import IO

REPO_ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = REPO_ROOT / "lean"
LAKEFILE = LEAN_DIR / "lakefile.toml"
LOCK_PATH = LEAN_DIR / ".lake" / "safe-lean-build.lock"

GIB = 1024**3
MIB = 1024**2
DEFAULT_MIN_PRESSURE_FREE_PERCENT = 15
DEFAULT_POLL_SECONDS = 2.0
DEFAULT_STATUS_SECONDS = 20.0
DEFAULT_WORKER_LIMIT_MIB = 32768
# Preflight uses a realistic high-water estimate.  The hard 32 GiB Lean cap is
# still enforced per process, while live telemetry handles the rare worker that
# exceeds this planning estimate.  On a 64 GiB machine this admits two workers
# (2 × 24 GiB + 12 GiB reserve) and rejects the crash-causing third worker.
DEFAULT_PLANNING_PEAK_MIB = 24576


@dataclass(frozen=True)
class MemorySnapshot:
    """System memory data available without privileged APIs."""

    total_bytes: int | None
    available_bytes: int | None
    pressure_free_percent: int | None
    swap_used_bytes: int | None


@dataclass(frozen=True)
class SafetyLimits:
    """Thresholds at which a build is refused or stopped."""

    reserve_bytes: int
    max_swap_bytes: int
    min_pressure_free_percent: int
    worker_limit_mib: int


def _run_text(command: Sequence[str], timeout: float = 3.0) -> str | None:
    """Run a small read-only system query, returning None when unavailable."""

    try:
        result = subprocess.run(
            command,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            timeout=timeout,
        )
    except (FileNotFoundError, PermissionError, subprocess.TimeoutExpired):
        return None
    return result.stdout if result.returncode == 0 else None


def _linux_meminfo() -> dict[str, int]:
    path = Path("/proc/meminfo")
    if not path.exists():
        return {}
    values: dict[str, int] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"([^:]+):\s+(\d+)\s+kB", line)
        if match:
            values[match.group(1)] = int(match.group(2)) * 1024
    return values


def _fallback_total_memory() -> int | None:
    try:
        pages = os.sysconf("SC_PHYS_PAGES")
        page_size = os.sysconf("SC_PAGE_SIZE")
    except (OSError, ValueError):
        return None
    return pages * page_size


def _parse_scaled_bytes(value: str, unit: str) -> int:
    factors = {"K": 1024, "M": MIB, "G": GIB, "T": 1024 * GIB}
    return int(float(value) * factors[unit.upper()])


def _darwin_snapshot() -> MemorySnapshot:
    total_output = _run_text(["sysctl", "-n", "hw.memsize"])
    total = int(total_output.strip()) if total_output and total_output.strip().isdigit() else None
    if total is None:
        total = _fallback_total_memory()

    available: int | None = None
    vm_output = _run_text(["vm_stat"])
    if vm_output:
        page_match = re.search(r"page size of (\d+) bytes", vm_output)
        page_size = int(page_match.group(1)) if page_match else 4096
        pages: dict[str, int] = {}
        for line in vm_output.splitlines():
            match = re.fullmatch(r'"?([^":]+)"?:\s+(\d+)\.', line.strip())
            if match:
                pages[match.group(1)] = int(match.group(2))
        reclaimable_names = (
            "Pages free",
            "Pages inactive",
            "Pages speculative",
            "Pages purgeable",
        )
        available = sum(pages.get(name, 0) for name in reclaimable_names) * page_size

    pressure_percent: int | None = None
    pressure_output = _run_text(["memory_pressure", "-Q"])
    if pressure_output:
        pressure_match = re.search(
            r"System-wide memory free percentage:\s*(\d+)%", pressure_output
        )
        if pressure_match:
            pressure_percent = int(pressure_match.group(1))

    swap_used: int | None = None
    swap_output = _run_text(["sysctl", "-n", "vm.swapusage"])
    if swap_output:
        swap_match = re.search(r"used\s*=\s*([0-9.]+)([KMGT])", swap_output)
        if swap_match:
            swap_used = _parse_scaled_bytes(swap_match.group(1), swap_match.group(2))

    return MemorySnapshot(total, available, pressure_percent, swap_used)


def _linux_snapshot() -> MemorySnapshot:
    values = _linux_meminfo()
    total = values.get("MemTotal") or _fallback_total_memory()
    available = values.get("MemAvailable")
    swap_used: int | None = None
    if "SwapTotal" in values and "SwapFree" in values:
        swap_used = max(0, values["SwapTotal"] - values["SwapFree"])
    return MemorySnapshot(total, available, None, swap_used)


def memory_snapshot() -> MemorySnapshot:
    system = platform.system()
    if system == "Darwin":
        return _darwin_snapshot()
    if system == "Linux":
        return _linux_snapshot()
    total = _fallback_total_memory()
    return MemorySnapshot(total, None, None, None)


def configured_worker_limit_mib() -> int:
    """Read Lean's ``-M`` ceiling so launcher and compiler cannot drift."""

    try:
        text = LAKEFILE.read_text(encoding="utf-8")
    except OSError:
        return DEFAULT_WORKER_LIMIT_MIB
    match = re.search(r'weakLeanArgs\s*=.*?"-M"\s*,\s*"(\d+)"', text, re.DOTALL)
    return int(match.group(1)) if match else DEFAULT_WORKER_LIMIT_MIB


def default_reserve_bytes(total_bytes: int | None) -> int:
    """Reserve about 20% of RAM, bounded to 2--12 GiB."""

    if total_bytes is None:
        return 12 * GIB
    return int(min(12 * GIB, max(2 * GIB, total_bytes * 0.20)))


def default_max_swap_bytes(total_bytes: int | None) -> int:
    """Stop long before the 63-swapfile state observed in the panic report."""

    if total_bytes is None:
        return 6 * GIB
    return int(min(6 * GIB, max(1 * GIB, total_bytes * 0.10)))


def default_jobs(total_bytes: int | None) -> int:
    """Use both performance clusters on large workstations without a third worker."""

    return 2 if total_bytes is not None and total_bytes >= 48 * GIB else 1


def parallelism_error(
    jobs: int,
    total_bytes: int | None,
    planning_peak_mib: int,
    reserve_bytes: int,
) -> str | None:
    """Reject aggregate planned peaks that consume OS headroom."""

    if jobs < 1:
        return "worker count must be at least 1"
    if jobs == 1 or total_bytes is None:
        return None
    aggregate = jobs * planning_peak_mib * MIB
    if aggregate + reserve_bytes <= total_bytes:
        return None
    return (
        f"{jobs} workers × {planning_peak_mib} MiB planned peak plus the "
        f"{reserve_bytes / GIB:.1f} GiB OS reserve exceeds "
        f"{total_bytes / GIB:.1f} GiB physical RAM"
    )


def process_tree_rss_bytes(root_pid: int) -> int | None:
    """Sum RSS for the launcher child and all descendants."""

    output = _run_text(["ps", "-axo", "pid=,ppid=,rss="])
    if output is None:
        return None
    rows: dict[int, tuple[int, int]] = {}
    for line in output.splitlines():
        fields = line.split()
        if len(fields) != 3:
            continue
        try:
            pid, parent_pid, rss_kib = (int(field) for field in fields)
        except ValueError:
            continue
        rows[pid] = (parent_pid, rss_kib * 1024)

    descendants = {root_pid}
    changed = True
    while changed:
        changed = False
        for pid, (parent_pid, _) in rows.items():
            if parent_pid in descendants and pid not in descendants:
                descendants.add(pid)
                changed = True
    return sum(rows[pid][1] for pid in descendants if pid in rows)


def pressure_reasons(
    snapshot: MemorySnapshot,
    build_rss_bytes: int | None,
    limits: SafetyLimits,
    baseline_swap_bytes: int = 0,
) -> list[str]:
    reasons: list[str] = []
    if snapshot.available_bytes is not None and snapshot.available_bytes <= limits.reserve_bytes:
        reasons.append(
            f"available memory {snapshot.available_bytes / GIB:.1f} GiB reached the "
            f"{limits.reserve_bytes / GIB:.1f} GiB reserve"
        )
    if (
        snapshot.pressure_free_percent is not None
        and snapshot.pressure_free_percent <= limits.min_pressure_free_percent
    ):
        reasons.append(
            f"macOS memory-pressure free percentage fell to "
            f"{snapshot.pressure_free_percent}%"
        )
    swap_growth = (
        max(0, snapshot.swap_used_bytes - baseline_swap_bytes)
        if snapshot.swap_used_bytes is not None
        else None
    )
    if swap_growth is not None and swap_growth >= limits.max_swap_bytes:
        reasons.append(
            f"swap grew by {swap_growth / GIB:.1f} GiB and reached the "
            f"{limits.max_swap_bytes / GIB:.1f} GiB per-build safety ceiling"
        )
    if (
        build_rss_bytes is not None
        and snapshot.total_bytes is not None
        and build_rss_bytes >= snapshot.total_bytes - limits.reserve_bytes
    ):
        reasons.append(
            f"Lean process-tree RSS {build_rss_bytes / GIB:.1f} GiB consumed the "
            "non-reserved physical-memory budget"
        )
    return reasons


def _format_snapshot(snapshot: MemorySnapshot, build_rss_bytes: int | None) -> str:
    parts: list[str] = []
    if snapshot.available_bytes is not None:
        parts.append(f"available={snapshot.available_bytes / GIB:.1f}GiB")
    if snapshot.pressure_free_percent is not None:
        parts.append(f"pressure-free={snapshot.pressure_free_percent}%")
    if snapshot.swap_used_bytes is not None:
        parts.append(f"swap={snapshot.swap_used_bytes / GIB:.1f}GiB")
    if build_rss_bytes is not None:
        parts.append(f"build-rss={build_rss_bytes / GIB:.1f}GiB")
    return ", ".join(parts) if parts else "memory telemetry unavailable"


def _stop_process_group(process: subprocess.Popen[bytes], reason: str) -> int:
    print(f"safe-lean: stopping build: {reason}", file=sys.stderr, flush=True)
    stages = ((signal.SIGINT, 8.0), (signal.SIGTERM, 5.0), (signal.SIGKILL, 2.0))
    for sig, timeout in stages:
        if process.poll() is not None:
            return process.returncode or 0
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            break
        try:
            return process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            continue
    return_code = process.poll()
    return return_code if return_code is not None else 75


@contextmanager
def _exclusive_build_lock() -> Iterator[None]:
    LOCK_PATH.parent.mkdir(parents=True, exist_ok=True)
    with LOCK_PATH.open("a+", encoding="utf-8") as handle:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            handle.seek(0)
            owner = handle.read().strip() or "unknown process"
            raise RuntimeError(f"another monitored Lean build is active ({owner})") from error
        handle.seek(0)
        handle.truncate()
        handle.write(f"pid={os.getpid()} started={time.strftime('%Y-%m-%dT%H:%M:%S%z')}\n")
        handle.flush()
        yield


def _positive_float(value: str) -> float:
    parsed = float(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def _jobs_from_environment() -> int | None:
    raw = os.environ.get("SAFE_LEAN_JOBS")
    if raw is None:
        return None
    try:
        return int(raw)
    except ValueError:
        return None


def _parse_arguments(argv: Sequence[str] | None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=_jobs_from_environment())
    parser.add_argument("--reserve-gib", type=_positive_float)
    parser.add_argument("--max-swap-gib", type=_positive_float)
    parser.add_argument(
        "--min-pressure-free-percent",
        type=int,
        default=DEFAULT_MIN_PRESSURE_FREE_PERCENT,
    )
    parser.add_argument("--poll-seconds", type=_positive_float, default=DEFAULT_POLL_SECONDS)
    parser.add_argument("--status-seconds", type=_positive_float, default=DEFAULT_STATUS_SECONDS)
    parser.add_argument("--log-file", type=Path)
    parser.add_argument("--check", type=Path, help="run one monitored `lake env lean` check")
    parser.add_argument("--dry-run", action="store_true", help="print preflight without launching")
    parser.add_argument("lake_args", nargs=argparse.REMAINDER)
    return parser.parse_args(argv)


def _build_command(arguments: argparse.Namespace, worker_limit_mib: int) -> list[str]:
    lake_args = list(arguments.lake_args)
    if lake_args[:1] == ["--"]:
        lake_args = lake_args[1:]
    if arguments.check is not None:
        if lake_args:
            raise ValueError("Lake build targets cannot be combined with --check")
        source = arguments.check.resolve()
        return [
            "lake",
            "env",
            "lean",
            "-s",
            "65536",
            "-M",
            str(worker_limit_mib),
            str(source),
        ]
    return ["lake", "build", *lake_args]


def _open_log(path: Path) -> IO[bytes]:
    return path.open("wb")


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parse_arguments(argv)
    initial = memory_snapshot()
    jobs = arguments.jobs if arguments.jobs is not None else default_jobs(initial.total_bytes)
    worker_limit_mib = configured_worker_limit_mib()
    reserve_bytes = (
        int(arguments.reserve_gib * GIB)
        if arguments.reserve_gib is not None
        else default_reserve_bytes(initial.total_bytes)
    )
    max_swap_bytes = (
        int(arguments.max_swap_gib * GIB)
        if arguments.max_swap_gib is not None
        else default_max_swap_bytes(initial.total_bytes)
    )
    limits = SafetyLimits(
        reserve_bytes=reserve_bytes,
        max_swap_bytes=max_swap_bytes,
        min_pressure_free_percent=arguments.min_pressure_free_percent,
        worker_limit_mib=worker_limit_mib,
    )

    concurrency_error = parallelism_error(
        jobs,
        initial.total_bytes,
        DEFAULT_PLANNING_PEAK_MIB,
        reserve_bytes,
    )
    if concurrency_error:
        print(f"safe-lean: refused unsafe configuration: {concurrency_error}", file=sys.stderr)
        return 64

    baseline_swap_bytes = initial.swap_used_bytes or 0
    preflight_reasons = pressure_reasons(
        initial, None, limits, baseline_swap_bytes=baseline_swap_bytes
    )
    if preflight_reasons:
        print(
            "safe-lean: refused to start under existing pressure: "
            + "; ".join(preflight_reasons),
            file=sys.stderr,
        )
        return 75

    try:
        command = _build_command(arguments, worker_limit_mib)
    except ValueError as error:
        print(f"safe-lean: {error}", file=sys.stderr)
        return 64

    print(
        "safe-lean: "
        f"jobs={jobs}, planned-peak={DEFAULT_PLANNING_PEAK_MIB}MiB/job, "
        f"hard-worker-limit={worker_limit_mib}MiB, "
        f"reserve={reserve_bytes / GIB:.1f}GiB, max-swap={max_swap_bytes / GIB:.1f}GiB",
        file=sys.stderr,
        flush=True,
    )
    print(f"safe-lean: command={' '.join(command)}", file=sys.stderr, flush=True)
    if arguments.dry_run:
        return 0

    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = str(jobs)
    environment["SAFE_LEAN_ACTIVE"] = "1"

    try:
        log_context: AbstractContextManager[IO[bytes] | None]
        if arguments.log_file is not None:
            log_context = _open_log(arguments.log_file)
        else:
            log_context = nullcontext(None)
        with _exclusive_build_lock(), log_context as log_handle:
            output_target: int | IO[bytes] | None = log_handle
            process = subprocess.Popen(
                command,
                cwd=LEAN_DIR,
                env=environment,
                stdout=output_target,
                stderr=subprocess.STDOUT if log_handle is not None else None,
                start_new_session=True,
            )
            violation_count = 0
            last_status = time.monotonic()
            while True:
                try:
                    return process.wait(timeout=arguments.poll_seconds)
                except subprocess.TimeoutExpired:
                    snapshot = memory_snapshot()
                    build_rss = process_tree_rss_bytes(process.pid)
                    reasons = pressure_reasons(
                        snapshot,
                        build_rss,
                        limits,
                        baseline_swap_bytes=baseline_swap_bytes,
                    )
                    violation_count = violation_count + 1 if reasons else 0
                    now = time.monotonic()
                    if now - last_status >= arguments.status_seconds:
                        print(
                            f"safe-lean: {_format_snapshot(snapshot, build_rss)}",
                            file=sys.stderr,
                            flush=True,
                        )
                        last_status = now
                    if violation_count >= 2:
                        _stop_process_group(process, "; ".join(reasons))
                        return 75
    except RuntimeError as error:
        print(f"safe-lean: refused to start: {error}", file=sys.stderr)
        return 75
    except KeyboardInterrupt:
        if "process" in locals():
            _stop_process_group(process, "interrupted by user")
        return 130
    except OSError as error:
        print(f"safe-lean: failed to launch: {error}", file=sys.stderr)
        return 74


if __name__ == "__main__":
    raise SystemExit(main())
