from scripts.safe_lean_build import (
    DEFAULT_PLANNING_PEAK_MIB,
    GIB,
    MemorySnapshot,
    SafetyLimits,
    default_jobs,
    default_max_swap_bytes,
    default_reserve_bytes,
    parallelism_error,
    pressure_reasons,
)


def test_m4_max_uses_two_workers_and_rejects_three() -> None:
    total = 64 * GIB
    reserve = default_reserve_bytes(total)

    assert default_jobs(total) == 2
    assert reserve == 12 * GIB
    assert parallelism_error(2, total, DEFAULT_PLANNING_PEAK_MIB, reserve) is None
    assert parallelism_error(3, total, DEFAULT_PLANNING_PEAK_MIB, reserve) is not None


def test_small_host_uses_one_worker_and_scaled_reserves() -> None:
    total = 8 * GIB

    assert default_jobs(total) == 1
    assert default_reserve_bytes(total) == 2 * GIB
    assert default_max_swap_bytes(total) == 1 * GIB


def test_pressure_guard_reports_available_pressure_swap_and_rss() -> None:
    limits = SafetyLimits(
        reserve_bytes=12 * GIB,
        max_swap_bytes=6 * GIB,
        min_pressure_free_percent=15,
        worker_limit_mib=32768,
    )
    snapshot = MemorySnapshot(
        total_bytes=64 * GIB,
        available_bytes=10 * GIB,
        pressure_free_percent=10,
        swap_used_bytes=7 * GIB,
    )

    reasons = pressure_reasons(snapshot, 53 * GIB, limits, baseline_swap_bytes=1 * GIB)

    assert len(reasons) == 4
    assert any("available memory" in reason for reason in reasons)
    assert any("memory-pressure" in reason for reason in reasons)
    assert any("swap grew" in reason for reason in reasons)
    assert any("process-tree RSS" in reason for reason in reasons)


def test_healthy_high_memory_snapshot_is_allowed() -> None:
    limits = SafetyLimits(
        reserve_bytes=12 * GIB,
        max_swap_bytes=6 * GIB,
        min_pressure_free_percent=15,
        worker_limit_mib=32768,
    )
    snapshot = MemorySnapshot(
        total_bytes=64 * GIB,
        available_bytes=18 * GIB,
        pressure_free_percent=22,
        swap_used_bytes=3 * GIB,
    )

    assert pressure_reasons(snapshot, 42 * GIB, limits) == []
