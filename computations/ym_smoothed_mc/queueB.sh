#!/bin/bash
cd /workspace/ymmc/p4_smoothed
R=runs
./run.sh $R/b2.85_L24x32_s6 3 --Ls 24 --Lt 32 --beta 2.85 --therm 600 --meas 800 --interval 5 --sides 5,6,7 --tflow 0,0.375,0.735,1.5,2.94,6.0 --seed 2851
