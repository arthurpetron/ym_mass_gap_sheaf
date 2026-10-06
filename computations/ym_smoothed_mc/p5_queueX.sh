#!/bin/bash
# P5 queue X (3 threads): new fine betas
cd /workspace/ymmc/p4_smoothed
F="--eps 0.05 --eps2 0.1 --tswitch2 2 --eps3 0.15"
./run.sh runs/b2.95_L32x48_s8 3 --Ls 32 --Lt 48 --beta 2.95 --therm 300 --meas 240 --interval 4 --sides 7,8,9 --tflow 0,2.66667,6,10.66667,16.66667,24 $F --seed 2951
python3 ana/p5_interim.py runs/b2.95_L32x48_s8 > runs/P5_INTERIM.md 2>&1
./run.sh runs/b3.00_L32x48_s10_A 3 --Ls 32 --Lt 48 --beta 3.0 --therm 300 --meas 170 --interval 4 --sides 9,10,11 --tflow 0,4.16667,9.375,16.66667,26.04167,37.5 $F --seed 3001
