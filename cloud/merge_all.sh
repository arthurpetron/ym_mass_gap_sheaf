#!/usr/bin/env bash
# Pull the per-shard JSONs from GCS and merge each (beta, L) point into the
# single analysis-ready glueball-/sigma- JSON the Python pipeline consumes.
# Run locally after the shards finish (or any time, to merge what's landed).
#
# Usage:
#   cloud/merge_all.sh [DEST_DIR]      # default DEST_DIR = visualizations/pilot/su2
#
# Env: PROJECT, BUCKET (default ${PROJECT}-ym-runs)

set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/.." && pwd)"
points="$here/points.tsv"

PROJECT="${PROJECT:-$(gcloud config get-value project 2>/dev/null)}"
BUCKET="${BUCKET:-${PROJECT}-ym-runs}"
dest="${1:-$repo/visualizations/pilot/su2}"
mkdir -p "$dest"

stage="$(mktemp -d)"
echo "staging shard JSONs from gs://${BUCKET}/runs -> $stage"
gsutil -m cp "gs://${BUCKET}/runs/glueball-*-s*.json" "$stage/" 2>/dev/null || true
gsutil -m cp "gs://${BUCKET}/runs/sigma-*-s*.json"    "$stage/" 2>/dev/null || true

while read -r beta L therm meas rmax sigma_smear bins seed_base shards; do
    [[ "$beta" == "beta" || -z "$beta" ]] && continue
    for kind in glueball sigma; do
        shopt -s nullglob
        parts=("$stage/${kind}-L${L}-b${beta}-s"*.json)
        shopt -u nullglob
        if (( ${#parts[@]} == 0 )); then
            echo "  -- ${kind} L=${L} b=${beta}: no shards yet, skipping"
            continue
        fi
        out="$dest/${kind}-L${L}-b${beta}.json"
        echo "  merging ${#parts[@]} ${kind} shards (L=${L} b=${beta}) -> $out"
        ( cd "$repo" && python -m computations.long_runs.merge_shards --out "$out" "${parts[@]}" )
    done
done < "$points"

echo "done.  analyze with e.g.:"
echo "  python -m computations.long_runs.glueball_analysis $dest/glueball-L24-b2.50.json --plot ..."
