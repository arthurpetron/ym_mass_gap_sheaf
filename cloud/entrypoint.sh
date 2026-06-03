#!/usr/bin/env bash
# Batch task entrypoint: one SHARD of one (beta, L) continuum point per task.
#
# A point is run as an array of `shards` independent Markov chains (distinct
# seeds), one per Batch task; the local `merge_shards.py` concatenates their
# configuration bins afterwards.  Each shard runs the COMBINED `measure` binary
# (glueball + Wilson loops on one chain) and CHECKPOINTS to the GCS-mounted
# output dir, so a preempted Spot VM resumes instead of restarting.
#
# Selection:
#   POINT_ROW          (env)  -> which data row of points.tsv this job targets
#   BATCH_TASK_INDEX   (env)  -> shard index within the point (0-based)
#
# So: submit one Batch job per point, with taskCount = that point's shard count.

set -euo pipefail

row_n="${POINT_ROW:?POINT_ROW not set (which points.tsv row this job runs)}"
shard="${BATCH_TASK_INDEX:?BATCH_TASK_INDEX not set (run me under Cloud Batch)}"
out="${OUT_DIR:-/mnt/disks/out}"
points="${POINTS_FILE:-/work/points.tsv}"
mkdir -p "$out"

# Fixed across the campaign (kept here, not in points.tsv, so the table is just
# the per-point physics knobs).
INTERVAL=5
OVERRELAX=4
SMEAR_LEVELS="0,8,16,24,32"
SMEAR_ALPHA=0.5
CKPT_SECS="${CKPT_SECS:-300}"   # checkpoint cadence (wall seconds)

# Select the data row (1-based POINT_ROW; row 0 = header is skipped).
read -r beta L therm meas rmax sigma_smear bins seed_base shards <<<"$(
    awk -v n="$row_n" 'NR>1 && (NR-1)==n' "$points"
)"
if [[ -z "${beta:-}" ]]; then
    echo "no points.tsv row $row_n" >&2
    exit 1
fi
if (( shard >= shards )); then
    echo "shard index $shard >= shards $shards for row $row_n -- nothing to do" >&2
    exit 1
fi

# Per-shard chain length (ceil division) and a unique seed per shard.
per_shard_meas=$(( (meas + shards - 1) / shards ))
seed=$(( seed_base + shard ))

g="$out/glueball-L${L}-b${beta}-s${shard}.json"
s="$out/sigma-L${L}-b${beta}-s${shard}.json"
ckpt="$out/ckpt-L${L}-b${beta}-s${shard}.bin"

echo "=== [row $row_n shard $shard/$shards] beta=$beta L=$L seed=$seed  start $(date -u) ==="
echo ">>> measure: $per_shard_meas meas / $therm therm  (every $INTERVAL), Rmax=$rmax  ($(nproc) cores)"

# The binary resumes from $ckpt if present (Spot preemption -> Batch retry).
measure \
    --L "$L" --beta "$beta" \
    --therm "$therm" --meas "$per_shard_meas" --interval "$INTERVAL" \
    --overrelax "$OVERRELAX" \
    --smear-levels "$SMEAR_LEVELS" --smear-alpha "$SMEAR_ALPHA" \
    --rmax "$rmax" --tmax "$rmax" --sigma-smear "$sigma_smear" \
    --bins "$bins" --seed "$seed" --shard "$shard" --nshards "$shards" \
    --checkpoint "$ckpt" --ckpt-secs "$CKPT_SECS" \
    --out-glueball "$g" --out-sigma "$s"

echo "=== [row $row_n shard $shard] done $(date -u) ==="
echo "    wrote $g"
echo "    wrote $s"
