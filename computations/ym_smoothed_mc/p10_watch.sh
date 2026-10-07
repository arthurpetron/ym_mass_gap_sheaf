#!/bin/bash
# P10 auto-report watcher (detached). Every 5 min: runs/P10_STATUS.md; once nsub=40 side-3 W(E1) error <= 0.03 (N>=200): runs/P10_CHECKPOINT40.md (once);
# when the job has exited: runs/P10_FINAL_auto.md, then exit. Restart-safe.
cd /workspace/ymmc/p4_smoothed; D=runs/p10_ml_d4_b2.50_L16x32; echo $$ > $D/watch.pid
while true; do
  done_flag=0; grep -q '^exit ' $D/run.log 2>/dev/null && ! kill -0 $(cat $D/pid) 2>/dev/null && done_flag=1
  nice -n 5 python3 ana/p10_report.py $D --mode status --out runs/P10_STATUS.md >> $D/watch.log 2>&1
  if [ ! -f runs/P10_CHECKPOINT40.md ]; then
    hit=$(python3 -c "import json;s=json.load(open('$D/report_state.json'));v=s.get('nsub=40_s3');print(1 if v and s['N']>=200 and v[1]<=0.03 else 0)" 2>/dev/null)
    if [ "$hit" = 1 ]; then nice -n 5 python3 ana/p10_report.py $D --mode ckpt40 --out runs/P10_CHECKPOINT40.md >> $D/watch.log 2>&1; echo "$(date +%T) CHECKPOINT40 written" >> $D/watch.log; fi
  fi
  if [ $done_flag = 1 ]; then nice -n 5 python3 ana/p10_report.py $D --mode final --out runs/P10_FINAL_auto.md >> $D/watch.log 2>&1; echo "$(date +%T) FINAL written" >> $D/watch.log; exit 0; fi
  sleep 300
done
