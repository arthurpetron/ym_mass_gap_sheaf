#!/bin/bash
# runs after queueB: finite-volume check at the finest beta (L=32)
cd /workspace/ymmc/p4_smoothed
while pgrep -f queueB.sh > /dev/null; do sleep 20; done
./run.sh runs/b2.85_L32x32_s6 3 --Ls 32 --Lt 32 --beta 2.85 --therm 500 --meas 600 --interval 5 --sides 5,6,7 --tflow 0,0.375,0.735,1.5,2.94,6.0 --seed 2852
