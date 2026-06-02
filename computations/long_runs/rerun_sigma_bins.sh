#!/usr/bin/env bash
# Re-measure the string-tension points with the per-bin output (added 2026-05-29)
# so sigma a^2 carries a genuine CONFIGURATION jackknife error instead of only
# the Cornell-fit covariance.  Same parameters/seeds as continuum_scan.sh, so
# the seed-deterministic MC reproduces the original configs (central values
# unchanged) and merely adds the bin sums -- EXCEPT beta=2.4, whose original
# seed was not recorded, so it is a fresh independent sample (consistent within
# errors).  The matched-volume beta=2.5/L22 point is produced WITH bins by the
# continuum_extend_b25.sh run directly (the binary now defaults to --bins 50).
#
# Sequential by design (each run saturates all cores).  Run AFTER the b2.5 job.
# Run detached:
#   nohup bash computations/long_runs/rerun_sigma_bins.sh > rerun_sigma.log 2>&1 &

set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root

PY=.venv/bin/python
ST=simulations/target/release/string_tension
OUT=visualizations/pilot/su2

# rerun_sigma  L beta therm meas rmax seed rmin
rerun_sigma () {
  local L=$1 beta=$2 therm=$3 meas=$4 rmax=$5 seed=$6 rmin=$7
  local s="$OUT/sigma-L${L}-b${beta}.json"
  echo ">>> [beta=$beta L=$L] string tension (binned): $meas meas / $therm therm, Rmax=$rmax   ($(date +%H:%M:%S))"
  $ST --L "$L" --beta "$beta" --therm "$therm" --meas "$meas" --interval 5 \
      --overrelax 4 --rmax "$rmax" --tmax "$rmax" --smear 4 --smear-alpha 0.5 \
      --bins 50 --seed "$seed" --out "$s"
  $PY -m computations.long_runs.string_tension_analysis "$s" --rmin "$rmin" --plot "${s%.json}.svg"
}

echo "=== rerun sigma with per-bin jackknife: start $(date) ==="

# --- Matched-volume series (PRIORITY: this is the headline continuum extrapolation) ---
#            L   beta  therm  meas   rmax seed rmin
rerun_sigma  12  2.3   2500   30000  5    27   2
rerun_sigma  16  2.4   3000   30000  8    41   3   # fresh seed (original not recorded)
rerun_sigma  18  2.45  3000   30000  8    29   3

# --- Fixed-L16 series (secondary; exposes the finite-volume systematic) ---
rerun_sigma  16  2.3   2500   30000  7    21   3
rerun_sigma  16  2.5   3000   30000  7    23   3
rerun_sigma  16  2.6   4000   30000  7    25   3

echo "=== rerun sigma done $(date) ==="
echo "NOTE: rebuild the continuum trends after enhancing continuum_trend.py to"
echo "      consume the jackknife sigma error (deferred until all points binned)."
