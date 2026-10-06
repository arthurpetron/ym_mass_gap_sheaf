#!/bin/bash
cd /workspace/ymmc/p4_smoothed
R=runs
./run.sh $R/b2.50_L24x32_s2 3 --Ls 24 --Lt 32 --beta 2.5 --therm 400 --meas 1000 --interval 3 --sides 1,2,3 --tflow 0,0.04167,0.08167,0.16667,0.32667,0.66667 --seed 2501
./run.sh $R/b2.50_L8x32_s2 3 --Ls 8 --Lt 32 --beta 2.5 --therm 400 --meas 2000 --interval 3 --sides 1,2,3 --tflow 0,0.04167,0.08167,0.16667,0.32667,0.66667 --seed 2502
./run.sh $R/b2.70_L16x32_s4 3 --Ls 16 --Lt 32 --beta 2.7 --therm 500 --meas 1000 --interval 4 --sides 3,4,5 --tflow 0,0.16667,0.32667,0.66667,1.30667,2.66667 --seed 2701
./run.sh $R/b2.70_L24x32_s4 3 --Ls 24 --Lt 32 --beta 2.7 --therm 500 --meas 800 --interval 4 --sides 3,4,5 --tflow 0,0.16667,0.32667,0.66667,1.30667,2.66667 --seed 2702
