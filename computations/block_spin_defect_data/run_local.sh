#!/usr/bin/env bash
# Local (Mac cores) block-spin defect production runs. NO cloud.
# Generates decorrelated SU(2) configs and measures correlated fine-vs-blocked
# Wilson loops + plaquette for lambda in {0.0, 0.5, 1.0}, per beta.
set -euo pipefail
OUT="$(cd "$(dirname "$0")" && pwd)"
cd "$OUT/../../simulations"
BIN=./target/release/block_defect
L="${1:-16}"
MEAS="${2:-12000}"
THERM="${3:-1000}"
LAMBDAS="0.0,0.5,1.0"
for BETA in 2.0 2.2 2.3 2.4 2.5; do
  echo "### L=$L beta=$BETA ###"
  $BIN --L "$L" --beta "$BETA" --therm "$THERM" --meas "$MEAS" --interval 4 \
       --overrelax 4 --rmax 6 --lambdas "$LAMBDAS" --bins 40 --seed 12345 \
       --out "$OUT/bdef-L${L}-b${BETA}.json"
done
echo "DONE L=$L"
