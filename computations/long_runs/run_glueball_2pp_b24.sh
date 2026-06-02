#!/usr/bin/env bash
# 2++ representative measurement: SU(2) glueball at the matched-vol anchor
# point (beta=2.4, L=16), 60k configs.  The (extended) Rust glueball binary
# now produces BOTH the 0++ A_1 correlator AND the 2++ E correlator from the
# same configs, so the m(2++)/m(0++) ratio comes out same-sample.
#
# Output goes to a new path (-2pp suffix) so the existing 0++ matched-vol
# anchor (glueball-L16-b2.4-hi.json, used by the continuum extrapolation)
# is NOT overwritten.  Continuum SU(2) reference (Teper): m(2++)/m(0++) ~ 1.45.
#
# Run detached:
#   nohup bash computations/long_runs/run_glueball_2pp_b24.sh > gb2pp_b24.log 2>&1 &

set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root

PY=.venv/bin/python
GB=simulations/target/release/glueball
OUT=visualizations/pilot/su2
SMEAR="0,8,16,24,32"

g="$OUT/glueball-L16-b2.4-2pp.json"

echo "=== 2++ glueball at matched-vol anchor (L=16, beta=2.4): start $(date) ==="
echo ">>> glueball with A_1 + E channels (300000 meas / 3000 therm)   ($(date +%H:%M:%S))"
$GB --L 16 --beta 2.4 --therm 3000 --meas 300000 --interval 5 \
    --overrelax 4 --smear-levels "$SMEAR" --smear-alpha 0.5 --bins 50 \
    --seed 43 --out "$g"

echo ">>> analyze 0++ A_1 channel"
$PY -m computations.long_runs.glueball_analysis "$g" --plot "${g%.json}-0pp.svg"

echo ">>> analyze 2++ E channel + m(2++)/m(0++)"
$PY -m computations.long_runs.gevp_2pp "$g" --plot "${g%.json}-2pp.svg"

echo "=== 2++ representative run done $(date) ==="
