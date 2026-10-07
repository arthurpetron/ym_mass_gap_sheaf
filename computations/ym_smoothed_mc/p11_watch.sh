#!/bin/bash
# P11 auto-report watcher (detached), parametrized copy of p10_watch.sh.
# usage: p11_watch.sh <rundir> <tag> <nmeas>   e.g. p11_watch.sh runs/p11_ml_d4_b2.70_L24x32 P11_B270 1500
# Every 5 min: runs/<tag>_STATUS.md; once nsub=40 side-3 W(E1) error <= 0.03 (N>=200): runs/<tag>_CHECKPOINT40.md (once);
# when the job has exited: runs/<tag>_FINAL_auto.md, then exit. Restart-safe. MC numerics only; not proof.
cd /workspace/ymmc/p4_smoothed; D=$1; T=$2; NM=$3; echo $$ > $D/watch.pid
R="nice -n 5 python3 ana/p10_report.py $D --tag $T --norefs --direct none --nmeas $NM"
while true; do
  done_flag=0; grep -q '^exit ' $D/run.log 2>/dev/null && ! kill -0 $(cat $D/pid) 2>/dev/null && done_flag=1
  [ -s $D/data.bin ] && $R --mode status --out runs/${T}_STATUS.md >> $D/watch.log 2>&1
  if [ ! -f runs/${T}_CHECKPOINT40.md ] && [ -f $D/report_state.json ]; then
    hit=$(python3 -c "import json;s=json.load(open('$D/report_state.json'));v=s.get('nsub=40_s3');print(1 if v and s['N']>=200 and v[1]<=0.03 else 0)" 2>/dev/null)
    if [ "$hit" = 1 ]; then $R --mode ckpt40 --out runs/${T}_CHECKPOINT40.md >> $D/watch.log 2>&1; echo "$(date +%T) CHECKPOINT40 written" >> $D/watch.log; fi
  fi
  if [ $done_flag = 1 ]; then $R --mode final --out runs/${T}_FINAL_auto.md >> $D/watch.log 2>&1; echo "$(date +%T) FINAL written" >> $D/watch.log; exit 0; fi
  sleep 300
done
