# Lean build safety and the 2026-08-02 postmortem

## Incident

At 08:10:52 PDT on 2026-08-02, `make lean-audit` started a full `lake build`
with `LEAN_NUM_THREADS=3`. The 64 GiB M4 Max permitted every Lean worker up to
32 GiB through `weakLeanArgs = ["-M", "32768"]`, an aggregate theoretical
allowance of 96 GiB before macOS and other applications.

At 08:18, macOS kernel-panicked. The panic record reported:

- no `watchdogd` check-in for 91 seconds;
- 63 swapfiles; and
- 100% of the compressor segment limit, marked `BAD`.

The immediate cause was therefore aggregate Lean concurrency under severe
compression/swap pressure. The old Makefile comment still assumed a 20 GiB
per-worker limit after the actual limit had been raised to 32 GiB.

## Enforced operating policy

`scripts/safe_lean_build.py` is now the sole supported Lean launcher. On the
64 GiB development Mac it is intentionally performance-oriented:

- two workers by default;
- a realistic 24 GiB planning peak per worker;
- the existing hard 32 GiB Lean ceiling per worker;
- 12 GiB reserved for macOS and interactive applications;
- a stop threshold at 15% macOS pressure-free capacity;
- a 6 GiB per-build swap-growth ceiling;
- telemetry every two seconds, with two consecutive threshold violations
  required before shutdown; and
- a repository lock preventing overlapping Lean builds.

This allows ordinary 3--4 GiB certificate jobs to run concurrently and lets a
single heavy certificate use most of its 32 GiB allowance. Three workers are
rejected on this machine. If two unusually large jobs overlap, the launcher
stops their entire process group before the machine enters the panic regime;
the already-produced `.olean` artifacts remain available for a one-worker
resume.

Smaller CI hosts automatically use one worker and proportionally smaller RAM
and swap reserves.

## Supported commands

```bash
# Full default build: two monitored workers on the 64 GiB Mac
make lean-build

# Narrow target
python3 scripts/safe_lean_build.py -- +YMGap.Continuum.ModuleName:olean

# Monitored single-file elaboration
python3 scripts/safe_lean_build.py --check lean/YMGap/Continuum/ModuleName.lean

# Resume a pressure-stopped or known-heavy build sequentially
python3 scripts/safe_lean_build.py --jobs 1 -- +YMGap.Continuum.ModuleName:olean

# Check one source and emit only its importable olean
python3 scripts/safe_lean_build.py --check lean/YMGap/Continuum/ModuleName.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/ModuleName.olean

# Inspect the resolved policy without starting Lean
python3 scripts/safe_lean_build.py --dry-run -- YMGap
```

All Makefile Lean targets, `lean_axiom_audit.py`, `frontier_status.py --lake`,
and `computations/progress_metric.sh` route through this launcher. Audit output
is spooled to disk instead of being retained in Python memory during the Lean
high-water mark.

Bare `lake build` and `lake env lean` bypass the monitor and are prohibited.

## Bounded certificate decomposition

The cold-cache rebuild also exposed several 64-term reflection checks whose
single `decide` proof reached Lean's per-worker kernel memory ceiling even
under safe one-worker execution.  These checks now use the same mathematical
decision procedure in bounded pieces: a checked literal raw polynomial, two
independent 32-term source equalities, a reassembly theorem, and a separate
reflected-target canonical equality.  This is a resource-safety refactor, not
an oracle: every piece remains kernel checked and its exported gates depend
only on `propext` and `Quot.sound`.
