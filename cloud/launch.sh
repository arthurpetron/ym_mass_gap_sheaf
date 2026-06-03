#!/usr/bin/env bash
# Submit one Cloud Batch job per (beta, L) point, each as an array of
# independent Spot shards (see entrypoint.sh / points.tsv).  Render the
# batch-job.json template per point and submit.
#
# Usage:
#   cloud/launch.sh                 # launch every point row in points.tsv
#   cloud/launch.sh 4 5 6           # launch only rows 4,5,6 (the heavy points)
#
# Env (with defaults):
#   PROJECT   gcloud config project        REGION   us-central1
#   BUCKET    ${PROJECT}-ym-runs           REPO     ym-sim
#   MACHINE   c2d-standard-16              MAX_PARALLEL   (per-point cap; default = shards)
#
# Quota note: N concurrent shards need N * vCPU(MACHINE) Spot vCPUs in REGION.
# If your SPOT/PREEMPTIBLE_CPUS quota is small, either raise it or set
# MAX_PARALLEL (and/or a smaller MACHINE) so shards queue instead of failing.

set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
points="$here/points.tsv"
template="$here/batch-job.json"

PROJECT="${PROJECT:-$(gcloud config get-value project 2>/dev/null)}"
REGION="${REGION:-us-central1}"
REPO="${REPO:-ym-sim}"
BUCKET="${BUCKET:-${PROJECT}-ym-runs}"
MACHINE="${MACHINE:-c2d-standard-16}"
PROVISIONING="${PROVISIONING:-SPOT}"        # SPOT (cheap, preemptible) or STANDARD
MEAS_OVERRIDE="${MEAS_OVERRIDE:-0}"         # >0 overrides points.tsv `meas` (smoke/budget)
THERM_OVERRIDE="${THERM_OVERRIDE:-0}"       # >0 overrides points.tsv `therm`
IMAGE="${REGION}-docker.pkg.dev/${PROJECT}/${REPO}/ym-sim:latest"

vcpu="${MACHINE##*-}"                 # e.g. c2d-standard-16 -> 16
cpu_milli=$(( vcpu * 1000 ))
mem_mib=$(( vcpu * 1024 ))            # 1 GiB/vCPU reservation; the VM has more

rows=("$@")
if (( ${#rows[@]} == 0 )); then
    rows=($(awk 'NR>1 {print NR-1}' "$points"))
fi

for row in "${rows[@]}"; do
    read -r beta L therm meas rmax sigma_smear bins seed_base shards <<<"$(
        awk -v n="$row" 'NR>1 && (NR-1)==n' "$points"
    )"
    [[ -z "${beta:-}" ]] && { echo "no row $row in points.tsv" >&2; continue; }
    parallel="${MAX_PARALLEL:-$shards}"
    (( parallel > shards )) && parallel="$shards"

    job="ym-c-l${L}-b${beta//./}"     # e.g. ym-c-l24-b25  (hyphens/digits only)
    tmp="$(mktemp)"
    sed -e "s|__IMAGE_URI__|${IMAGE}|g" \
        -e "s|__BUCKET_NAME__|${BUCKET}|g" \
        -e "s|__POINT_ROW__|${row}|g" \
        -e "s|__TASK_COUNT__|${shards}|g" \
        -e "s|__PARALLELISM__|${parallel}|g" \
        -e "s|__MACHINE_TYPE__|${MACHINE}|g" \
        -e "s|__CPU_MILLI__|${cpu_milli}|g" \
        -e "s|__MEM_MIB__|${mem_mib}|g" \
        -e "s|__PROVISIONING__|${PROVISIONING}|g" \
        -e "s|__MEAS_OVERRIDE__|${MEAS_OVERRIDE}|g" \
        -e "s|__THERM_OVERRIDE__|${THERM_OVERRIDE}|g" \
        "$template" | grep -v '"_comment"' > "$tmp"

    echo "==> row $row: beta=$beta L=$L  shards=$shards parallel=$parallel machine=$MACHINE prov=$PROVISIONING  job=$job"
    gcloud batch jobs submit "$job" \
        --location="$REGION" --config="$tmp"
    rm -f "$tmp"
done
