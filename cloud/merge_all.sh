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

# Each (beta, L) point may have been run under several campaign tags: the base
# run (no tag) plus any `TAG`-suffixed high-statistics reruns (e.g. `-hi`, see
# launch.sh / entrypoint.sh, which name shards `<kind>-L<L>-b<beta><TAG>-s<n>`).
# We auto-discover every tag present for each point and merge each into its own
# correctly-named output, so tagged runs are never silently skipped.  points.tsv
# can also list the same (beta, L) twice (e.g. a base row and a -hi row), so we
# process each (beta, L) only once -- the tag discovery already covers both.
processed=""
while read -r beta L therm meas rmax sigma_smear bins seed_base shards; do
    [[ "$beta" == "beta" || -z "$beta" ]] && continue
    key="L${L}-b${beta}"
    case " $processed " in *" $key "*) continue ;; esac
    processed="$processed $key"

    for kind in glueball sigma; do
        prefix="${kind}-L${L}-b${beta}"
        # Distinct tags for this point, one token per tag.  The base (untagged)
        # run is emitted as the bare token "X"; a tag `-hi` as "X-hi".  This keeps
        # the empty base tag distinguishable from "no shards at all".
        tokens="$(
            shopt -s nullglob
            for f in "$stage/${prefix}"*-s*.json; do
                rest="${f##*/}"; rest="${rest#${prefix}}"   # e.g. "-hi-s3.json" or "-s3.json"
                tag="${rest%-s*}"                            # "-hi", "", or "5-hi" (wrong beta)
                shardpart="${rest#"$tag"}"                   # "-s3.json"
                [[ "$shardpart" =~ ^-s[0-9]+\.json$ ]] || continue
                # valid tag is empty (base) or -<alpha><alnum...>; reject a digit
                # lead-in, which means b${beta} prefix-matched a longer beta.
                [[ -z "$tag" || "$tag" =~ ^-[A-Za-z][A-Za-z0-9]*$ ]] || continue
                printf 'X%s\n' "$tag"
            done | sort -u
        )"
        if [[ -z "$tokens" ]]; then
            echo "  -- ${kind} L=${L} b=${beta}: no shards yet, skipping"
            continue
        fi
        while IFS= read -r tok; do
            [[ -z "$tok" ]] && continue
            tag="${tok#X}"
            shopt -s nullglob
            parts=("$stage/${prefix}${tag}-s"*.json)
            shopt -u nullglob
            (( ${#parts[@]} == 0 )) && continue
            out="$dest/${prefix}${tag}.json"
            echo "  merging ${#parts[@]} ${kind} shards (L=${L} b=${beta} tag='${tag:-<base>}') -> $out"
            ( cd "$repo" && python -m computations.long_runs.merge_shards --out "$out" "${parts[@]}" )
        done <<< "$tokens"
    done
done < "$points"

echo "done.  analyze with e.g.:"
echo "  python -m computations.long_runs.glueball_analysis $dest/glueball-L24-b2.50.json --plot ..."
