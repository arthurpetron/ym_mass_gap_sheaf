#!/usr/bin/env bash
# Continuum trend for m(0++)/sqrt(sigma): TWO complementary beta series, both
# anchored on the existing beta=2.4 (L=16, 60k-config) measurement.
#
#  Series A -- FIXED L=16 (beta is the only thing changing).  Finite-volume
#    effects grow as beta rises (the physical box shrinks), so this shows the
#    raw beta-dependence and, by contrast with series B, exposes the
#    finite-volume systematic directly.
#       beta = 2.3, 2.4*, 2.5, 2.6      (* reused)
#
#  Series B -- MATCHED PHYSICAL VOLUME (L grows with beta to hold L*sqrt(sigma)a
#    ~ 4.3-4.7).  Finite-volume effects stay roughly constant, so the a -> 0
#    extrapolation is clean.
#       beta = 2.3/L12, 2.4*/L16, 2.45/L18
#    (the matched beta=2.5/L22 point would be ~5 h at 60k configs on its own and
#     is omitted here; run it separately if you want the matched series finer.)
#
# Glueball runs target 60,000 configs (interval 5 => meas 300000); the matched
# L=18 point is 40,000 to keep the total near ~7 h.  Each beta runs the binned
# glueball + string tension, analyzes both, then two continuum extrapolations.
# Sequential by design: every run already saturates all cores.
#
# Run detached:
#   nohup bash computations/long_runs/continuum_scan.sh > scan.log 2>&1 &

set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root

PY=.venv/bin/python
GB=simulations/target/release/glueball
ST=simulations/target/release/string_tension
OUT=visualizations/pilot/su2
SMEAR="0,8,16,24,32"

run_point () {
  local beta=$1 L=$2 gmeas=$3 gtherm=$4 smeas=$5 stherm=$6 rmax=$7 rmin=$8 seed=$9
  local g="$OUT/glueball-L${L}-b${beta}.json"
  local s="$OUT/sigma-L${L}-b${beta}.json"
  echo ">>> [beta=$beta L=$L] glueball: $gmeas meas / $gtherm therm   ($(date +%H:%M:%S))"
  $GB --L "$L" --beta "$beta" --therm "$gtherm" --meas "$gmeas" --interval 5 \
      --overrelax 4 --smear-levels "$SMEAR" --smear-alpha 0.5 --bins 50 \
      --seed "$seed" --out "$g"
  echo ">>> [beta=$beta L=$L] string tension: $smeas meas / $stherm therm, Rmax=$rmax   ($(date +%H:%M:%S))"
  $ST --L "$L" --beta "$beta" --therm "$stherm" --meas "$smeas" --interval 5 \
      --overrelax 4 --rmax "$rmax" --tmax "$rmax" --smear 4 --smear-alpha 0.5 \
      --seed "$seed" --out "$s"
  echo ">>> [beta=$beta L=$L] analyze"
  $PY -m computations.long_runs.glueball_analysis "$g" --plot "${g%.json}.svg"
  $PY -m computations.long_runs.string_tension_analysis "$s" --rmin "$rmin" --plot "${s%.json}.svg"
}

echo "=== continuum scan start: $(date) ==="

#          beta   L  g_meas  g_therm  s_meas  s_therm  rmax  rmin  seed
# Series A: fixed L=16 (beta-only)
run_point  2.3    16  300000   3000    30000    2500     7     3    21
run_point  2.5    16  300000   4000    30000    3000     7     3    23
run_point  2.6    16  300000   5000    30000    4000     7     3    25
# Series B: matched volume (new points; beta=2.4/L16 shared with series A)
run_point  2.3    12  300000   3000    30000    2500     5     2    27
run_point  2.45   18  200000   4000    30000    3000     8     3    29

echo "=== extrapolations: $(date) ==="

cat > "$OUT/continuum-fixedL16.json" <<JSON
{"teper": 3.74,
 "points": [
   {"beta": 2.3, "glue": "$OUT/glueball-L16-b2.3.json",    "sigma": "$OUT/sigma-L16-b2.3.json", "rmin": 3},
   {"beta": 2.4, "glue": "$OUT/glueball-L16-b2.4-hi.json", "sigma": "$OUT/sigma-L16-b2.4.json", "rmin": 3},
   {"beta": 2.5, "glue": "$OUT/glueball-L16-b2.5.json",    "sigma": "$OUT/sigma-L16-b2.5.json", "rmin": 3},
   {"beta": 2.6, "glue": "$OUT/glueball-L16-b2.6.json",    "sigma": "$OUT/sigma-L16-b2.6.json", "rmin": 3}
 ]}
JSON

cat > "$OUT/continuum-matchedvol.json" <<JSON
{"teper": 3.74,
 "points": [
   {"beta": 2.3,  "glue": "$OUT/glueball-L12-b2.3.json",    "sigma": "$OUT/sigma-L12-b2.3.json",  "rmin": 2},
   {"beta": 2.4,  "glue": "$OUT/glueball-L16-b2.4-hi.json", "sigma": "$OUT/sigma-L16-b2.4.json",  "rmin": 3},
   {"beta": 2.45, "glue": "$OUT/glueball-L18-b2.45.json",   "sigma": "$OUT/sigma-L18-b2.45.json", "rmin": 3}
 ]}
JSON

echo "--- Series A: fixed L=16 (beta-only) ---"
$PY -m computations.long_runs.continuum_trend "$OUT/continuum-fixedL16.json" \
    --plot "$OUT/continuum-trend-fixedL16.svg"
echo "--- Series B: matched physical volume ---"
$PY -m computations.long_runs.continuum_trend "$OUT/continuum-matchedvol.json" \
    --plot "$OUT/continuum-trend-matchedvol.svg"

echo "=== continuum scan done: $(date) ==="
