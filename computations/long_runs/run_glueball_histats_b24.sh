#!/usr/bin/env bash
# High-statistics glueball run at the matched-vol anchor (beta=2.4, L=16):
# 3x the configurations of the 60k anchor (180k) so the first-excited 0++ gap
# (m_1 - m_0)a, currently 0.59(15) ~ 3.8 sigma, sharpens by sqrt(3) to >6 sigma.
# The gap is read at a single tau, so its error is pure 1/sqrt(N); 3x stats also
# raises the tau=2 signal-to-noise by sqrt(3) in both the 0++ and 2++ channels.
#
# Basis note: this run KEEPS the proven 5-level APE basis 0,8,16,24,32.  A
# basis-conditioning study (computations/long_runs/, seed-44 8k-config probe)
# showed the smeared plaquette operators at this beta are strongly collinear:
# C(tau0)'s condition number rises ~9e5 -> 1e7 -> 1e9 from 5 -> 6 -> 7 levels
# and the matrix goes singular (excited GEVP eigenvalue NaN) by 9 levels.  More
# APE radii add near-duplicates, not independent operators, so widening the
# smearing basis does NOT help -- genuine enrichment needs different operator
# SHAPES (rectangular / larger Wilson loops), an engine addition tracked
# separately.  Statistics, not basis, is the working lever here.
#
# The (extended) glueball binary emits BOTH the 0++ A_1 and 2++ E correlators
# from the same configs, so this single run improves the excited 0++, the 2++
# ratio, and the blocking certification together.  New independent seed (44);
# output goes to a -histat path so the existing anchor JSONs are untouched.
# Expected wall time ~4.3 h on 16 threads.
#
# Run detached:
#   nohup bash computations/long_runs/run_glueball_histats_wide_b24.sh \
#         > gb_histats_b24.log 2>&1 &

set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root

PY=.venv/bin/python
GB=simulations/target/release/glueball
OUT=visualizations/pilot/su2
SMEAR="0,8,16,24,32"

g="$OUT/glueball-L16-b2.4-histat.json"

echo "=== high-stats glueball (L=16, beta=2.4): start $(date) ==="
echo ">>> glueball A_1 + E channels, 180000 configs / 3000 therm, 5-level basis   ($(date +%H:%M:%S))"
$GB --L 16 --beta 2.4 --therm 3000 --meas 900000 --interval 5 \
    --overrelax 4 --smear-levels "$SMEAR" --smear-alpha 0.5 --bins 50 \
    --seed 44 --out "$g"

echo ">>> analyze 0++ A_1 channel"
$PY -m computations.long_runs.glueball_analysis "$g" --plot "${g%.json}-0pp.svg"

echo ">>> first-excited 0++ from the same GEVP"
$PY -m computations.long_runs.gevp_excited "$g" --plot "${g%.json}-excited.svg"

echo ">>> 2++ E channel + m(2++)/m(0++)"
$PY -m computations.long_runs.gevp_2pp "$g" --plot "${g%.json}-2pp.svg"

echo ">>> blocking certification of the 0++ error bar"
$PY -m computations.long_runs.autocorr_blocking "$g" \
    --plot "${g%.json}-blocking.svg" --out "${g%.json}-blocking.json"

echo "=== high-stats wide-basis run done $(date) ==="
