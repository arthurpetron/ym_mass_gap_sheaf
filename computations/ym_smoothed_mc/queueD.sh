#!/bin/bash
# runs after queueA: intermediate betas with odd sides
cd /workspace/ymmc/p4_smoothed
while pgrep -f queueA.sh > /dev/null; do sleep 20; done
./run.sh runs/b2.60_L24x32_s3 3 --Ls 24 --Lt 32 --beta 2.6 --therm 400 --meas 600 --interval 3 --sides 2,3,4 --tflow 0,0.09375,0.18375,0.375,0.735,1.5 --seed 2601
./run.sh runs/b2.80_L24x32_s5 3 --Ls 24 --Lt 32 --beta 2.8 --therm 500 --meas 600 --interval 5 --sides 4,5,6 --tflow 0,0.26042,0.51042,1.04167,2.04167,4.16667 --seed 2801
