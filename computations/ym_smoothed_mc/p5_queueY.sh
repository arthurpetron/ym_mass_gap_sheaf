#!/bin/bash
# P5 queue Y (3 threads): rho-scan reruns at existing betas, then a 2nd beta=3.0 chain
cd /workspace/ymmc/p4_smoothed
F="--eps 0.05 --eps2 0.1 --tswitch2 2 --eps3 0.15"
./run.sh runs/p5_b2.85_L24x32_s6 3 --Ls 24 --Lt 32 --beta 2.85 --therm 600 --meas 600 --interval 5 --sides 5,6,7 --tflow 0,1.5,3.375,6,9.375,13.5 $F --seed 2853
./run.sh runs/p5_b2.70_L24x32_s4 3 --Ls 24 --Lt 32 --beta 2.7 --therm 500 --meas 500 --interval 4 --sides 3,4,5 --tflow 0,0.66667,1.5,2.66667,4.16667,6.0 $F --seed 2703
./run.sh runs/p5_b2.60_L24x32_s3 3 --Ls 24 --Lt 32 --beta 2.6 --therm 400 --meas 500 --interval 3 --sides 2,3,4 --tflow 0,0.375,0.84375,1.5,2.34375,3.375 $F --seed 2603
./run.sh runs/p5_b2.50_L24x32_s2 3 --Ls 24 --Lt 32 --beta 2.5 --therm 400 --meas 600 --interval 3 --sides 1,2,3 --tflow 0,0.16667,0.375,0.66667,1.04167,1.5 $F --seed 2503
./run.sh runs/b3.00_L32x48_s10_B 3 --Ls 32 --Lt 48 --beta 3.0 --therm 300 --meas 170 --interval 4 --sides 9,10,11 --tflow 0,4.16667,9.375,16.66667,26.04167,37.5 $F --seed 3002
