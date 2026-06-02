#!/usr/bin/env bash
# Batch task entrypoint: one (beta, L) continuum point per task.
# Google Cloud Batch sets BATCH_TASK_INDEX (0-based) for each array task; we use
# it to select a data row from points.tsv and run the glueball + string-tension
# measurements, writing JSON to the GCS-mounted output directory.
#
# Same parameters/flags as computations/long_runs/continuum_scan.sh so the cloud
# output is drop-in compatible with the local Python analysis pipeline.

set -euo pipefail

idx="${BATCH_TASK_INDEX:?BATCH_TASK_INDEX not set (run me under Cloud Batch)}"
out="${OUT_DIR:-/mnt/disks/out}"
points="${POINTS_FILE:-/work/points.tsv}"
mkdir -p "$out"

# Select the idx-th data row (row 0 = header is skipped).
row="$(awk -v n="$idx" 'NR>1 && (NR-2)==n' "$points")"
if [[ -z "$row" ]]; then
  echo "no points.tsv row for BATCH_TASK_INDEX=$idx" >&2
  exit 1
fi
read -r beta L g_meas g_therm s_meas s_therm rmax rmin seed <<<"$row"

g="$out/glueball-L${L}-b${beta}.json"
s="$out/sigma-L${L}-b${beta}.json"

echo "=== [task $idx] beta=$beta L=$L  seed=$seed  start $(date -u) ==="
echo ">>> glueball: $g_meas meas / $g_therm therm  ($(nproc) cores)"
glueball --L "$L" --beta "$beta" --therm "$g_therm" --meas "$g_meas" --interval 5 \
    --overrelax 4 --smear-levels "0,8,16,24,32" --smear-alpha 0.5 --bins 50 \
    --seed "$seed" --out "$g"

echo ">>> string tension: $s_meas meas / $s_therm therm  Rmax=$rmax"
string_tension --L "$L" --beta "$beta" --therm "$s_therm" --meas "$s_meas" --interval 5 \
    --overrelax 4 --rmax "$rmax" --tmax "$rmax" --smear 4 --smear-alpha 0.5 --bins 50 \
    --seed "$seed" --out "$s"

echo "=== [task $idx] beta=$beta L=$L  done $(date -u) ==="
echo "    wrote $g"
echo "    wrote $s"
