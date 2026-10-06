#!/bin/bash
# P7 production: beta=2.95, Ls=Lt=48, side 8 (sides 7,8,9), same rho/tflow set as b2.95_L32x48_s8.
# usage: p7_queue.sh [--resume]   (run detached: setsid nohup bash p7_queue.sh > runs/p7_queue.log 2>&1 &)
cd /workspace/ymmc/p4_smoothed
dir=runs/b2.95_L48x48_s8; mkdir -p $dir/cfg; tf=$dir/threads; FULL=4; LOW=3; MEAS=240
[ -f $tf ] || echo $FULL > $tf
ARGS="--Ls 48 --Lt 48 --beta 2.95 --therm 1000 --therm-ckpt 100 --meas $MEAS --interval 4 --overrelax 4 --sides 7,8,9 --tflow 0,2.66667,6,10.66667,16.66667,24 --eps 0.05 --eps2 0.1 --tswitch2 2 --eps3 0.15 --seed 2953 --ckpt 5 --save-every 3 --save-dir $dir/cfg --threads $FULL --threads-file $tf --out $dir/data"
{ echo "pre-run snapshot $(date '+%F %T %Z')"; echo "nproc --all: $(nproc --all)"; free -m; df -h / | tail -1; echo "loadavg: $(cat /proc/loadavg)"; echo "args: $ARGS $*"; } >> $dir/prerun_snapshot.txt
./target/release/p4run $ARGS "$@" >> $dir/run.log 2>&1 &
jp=$!; echo $jp > $dir/pid; echo "$(date '+%F %T') p4run pid $jp" 
bash sampler_p7.sh $jp $dir/resources.log $tf $FULL $LOW &
sp=$!
# monitor: auto-interim at >= MEAS/3 complete records, auto-final at end
nrec() { OMP_NUM_THREADS=1 python3 -c "import sys; sys.path.insert(0,'ana'); from load import load; print(len(load('$dir/data.bin')[1]))" 2>/dev/null || echo 0; }
while kill -0 $jp 2>/dev/null; do
  sleep 300
  if [ ! -f runs/P7_INTERIM.md ] && [ "$(nrec)" -ge $((MEAS/3)) ]; then
    echo "$(date '+%F %T') writing interim"; OMP_NUM_THREADS=1 nice -n 10 python3 ana/p7_interim.py $dir runs/P7_INTERIM.md >> runs/p7_queue.log 2>&1
  fi
done
wait $jp; rc=$?; echo "exit $rc $(date '+%F %T')" >> $dir/run.log
kill $sp 2>/dev/null; wait $sp 2>/dev/null; echo "# $(date +%T) run finished rc=$rc; sampler stopped" >> $dir/resources.log
OMP_NUM_THREADS=1 nice -n 10 python3 ana/p7_interim.py $dir runs/P7_FINAL_auto.md >> runs/p7_queue.log 2>&1
echo "$(date '+%F %T') queue done rc=$rc"
