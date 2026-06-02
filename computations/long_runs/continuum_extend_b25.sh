#!/usr/bin/env bash
# Extend the matched-physical-volume continuum series with the finer
# beta=2.5 / L=22 point (the affordable half of the extension cut from the main
# scan).  At this matched box (L*sqrt(sigma)a ~ 4.1) the torelon mass
# sigma*L*a ~ 0.78 sits ABOVE the glueball m_0 a ~ 0.68, so -- unlike beta=2.6
# at fixed L=16 -- it does not contaminate the 0++ ground state.
#
# Runs the binned glueball (60k configs) + string tension, analyzes both, then
# rebuilds the matched-volume extrapolation now including beta=2.5.
#
# Run detached:
#   nohup bash computations/long_runs/continuum_extend_b25.sh > extend_b25.log 2>&1 &

set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root

PY=.venv/bin/python
GB=simulations/target/release/glueball
ST=simulations/target/release/string_tension
OUT=visualizations/pilot/su2
SMEAR="0,8,16,24,32"

g="$OUT/glueball-L22-b2.5.json"
s="$OUT/sigma-L22-b2.5.json"

echo "=== extend matched-volume: beta=2.5 L=22 start $(date) ==="
echo ">>> glueball (300000 meas / 4000 therm)   ($(date +%H:%M:%S))"
$GB --L 22 --beta 2.5 --therm 4000 --meas 300000 --interval 5 \
    --overrelax 4 --smear-levels "$SMEAR" --smear-alpha 0.5 --bins 50 \
    --seed 31 --out "$g"
echo ">>> string tension (30000 meas / 3000 therm, Rmax=8)   ($(date +%H:%M:%S))"
$ST --L 22 --beta 2.5 --therm 3000 --meas 30000 --interval 5 \
    --overrelax 4 --rmax 8 --tmax 8 --smear 4 --smear-alpha 0.5 \
    --seed 31 --out "$s"
echo ">>> analyze"
$PY -m computations.long_runs.glueball_analysis "$g" --plot "${g%.json}.svg"
$PY -m computations.long_runs.string_tension_analysis "$s" --rmin 3 --plot "${s%.json}.svg"

echo "=== rebuild matched-volume extrapolation (now 4 points) $(date) ==="
cat > "$OUT/continuum-matchedvol.json" <<JSON
{"teper": 3.74,
 "points": [
   {"beta": 2.3,  "glue": "$OUT/glueball-L12-b2.3.json",    "sigma": "$OUT/sigma-L12-b2.3.json",  "rmin": 2},
   {"beta": 2.4,  "glue": "$OUT/glueball-L16-b2.4-hi.json", "sigma": "$OUT/sigma-L16-b2.4.json",  "rmin": 3},
   {"beta": 2.45, "glue": "$OUT/glueball-L18-b2.45.json",   "sigma": "$OUT/sigma-L18-b2.45.json", "rmin": 3},
   {"beta": 2.5,  "glue": "$OUT/glueball-L22-b2.5.json",    "sigma": "$OUT/sigma-L22-b2.5.json",  "rmin": 3}
 ]}
JSON

$PY -m computations.long_runs.continuum_trend "$OUT/continuum-matchedvol.json" \
    --plot "$OUT/continuum-trend-matchedvol.svg"

echo "=== extend done $(date) ==="
